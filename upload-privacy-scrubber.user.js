
 // ==UserScript==
 // @name         Upload Privacy Scrubber - DCInside / Arca.live / Reddit
 // @namespace    local.upload.privacy
 // @version      2.3.0
 // @description  Randomizes image filenames (IMG_XXXX) and removes metadata.
 // @match        https://*.dcinside.com/*
 // @match        https://arca.live/*
 // @match        https://*.reddit.com/*
 // @run-at       document-start
 // @sandbox      DOM
 // @grant        GM_notification
 // @downloadURL  https://raw.githubusercontent.com/gminshin/k-community-upload-privacy-scrubber/main/upload-privacy-scrubber.user.js
 // @updateURL    https://raw.githubusercontent.com/gminshin/k-community-upload-privacy-scrubber/main/upload-privacy-scrubber.user.js
 // ==/UserScript==

(() => {
    'use strict';

    const CANVAS_SAME_FORMAT = new Set([
        'image/png', 'image/jpeg'
    ]);

    const CONVERT_TO_PNG = new Set([
        'image/avif', 'image/bmp',
        'image/heic', 'image/heif'
    ]);

    const MAX_FILE_BYTES = 150 * 1024 * 1024;
    const MAX_PIXELS = 60_000_000;

    const syntheticEvents = new WeakSet();
    const inputStates = new WeakMap();

    const getRandomValues = crypto.getRandomValues.bind(crypto);

    const createImageBitmapSafe =
        typeof window.createImageBitmap === 'function'
            ? window.createImageBitmap.bind(window)
            : null;

    function notifyFailure(message) {
        try {
            if (typeof GM_notification === 'function') {
                GM_notification({
                    title: 'Upload Privacy Scrubber',
                    text: message,
                    timeout: 6000
                });
            }
        } catch (_) {}
    }

    // ============================================================
    // Random iPhone-style filenames
    // IMG_0001 through IMG_9999
    // No duplicate numbers within the current page session
    // ============================================================

    const usedImageNumbers = new Set();

    function randomFilename(extension) {
        if (usedImageNumbers.size >= 9999) {
            throw new Error('All IMG_0001-IMG_9999 filenames are used');
        }

        while (true) {
            const bytes = new Uint16Array(1);
            getRandomValues(bytes);

            // Rejection sampling prevents modulo bias.
            if (bytes[0] >= 59994) continue;

            const number = 1 + (bytes[0] % 9999);

            if (usedImageNumbers.has(number)) continue;

            usedImageNumbers.add(number);

            return `IMG_${String(number).padStart(4, '0')}${extension}`;
        }
    }

    // ============================================================
    // File format helpers
    // ============================================================

    function inferMime(file) {
        const declared = String(file.type || '')
            .trim().toLowerCase();

        if (declared.startsWith('image/')) {
            return declared;
        }

        const name = String(file.name || '').toLowerCase();

        if (/\.png$/.test(name)) return 'image/png';
        if (/\.(jpg|jpeg)$/.test(name)) return 'image/jpeg';
        if (/\.webp$/.test(name)) return 'image/webp';
        if (/\.gif$/.test(name)) return 'image/gif';
        if (/\.avif$/.test(name)) return 'image/avif';
        if (/\.bmp$/.test(name)) return 'image/bmp';
        if (/\.heic$/.test(name)) return 'image/heic';
        if (/\.heif$/.test(name)) return 'image/heif';
        if (/\.svg$/.test(name)) return 'image/svg+xml';

        return '';
    }

    function isImageCandidate(file) {
        if (!file) return false;

        const mime = inferMime(file);

        return (
            mime.startsWith('image/') ||
            /\.(png|jpe?g|webp|gif|avif|bmp|heic|heif|svg)$/i
                .test(file.name || '')
        );
    }

    function extensionForMime(mime) {
        switch (mime) {
            case 'image/png': return '.png';
            case 'image/jpeg': return '.jpg';
            case 'image/webp': return '.webp';
            case 'image/gif': return '.gif';
            default:
                throw new Error(
                    `Unexpected output MIME type: ${mime}`
                );
        }
    }

    function ascii(bytes, start, length) {
        let out = '';

        for (let i = start; i < start + length; i++) {
            out += String.fromCharCode(bytes[i]);
        }

        return out;
    }

    function concatChunks(chunks) {
        let total = 0;

        for (const chunk of chunks) {
            total += chunk.length;
        }

        const output = new Uint8Array(total);
        let offset = 0;

        for (const chunk of chunks) {
            output.set(chunk, offset);
            offset += chunk.length;
        }

        return output;
    }

    function readUint32LE(bytes, offset) {
        if (offset + 4 > bytes.length) {
            throw new Error('Unexpected end of data');
        }

        return (
            bytes[offset] |
            (bytes[offset + 1] << 8) |
            (bytes[offset + 2] << 16) |
            (bytes[offset + 3] << 24)
        ) >>> 0;
    }

    function writeUint32LE(bytes, offset, value) {
        bytes[offset] = value & 0xff;
        bytes[offset + 1] = (value >>> 8) & 0xff;
        bytes[offset + 2] = (value >>> 16) & 0xff;
        bytes[offset + 3] = (value >>> 24) & 0xff;
    }

    // ============================================================
    // GIF sanitizer
    // Preserves animation while removing optional metadata
    // ============================================================

    function endOfGifSubBlocks(bytes, position) {
        let pos = position;

        while (true) {
            if (pos >= bytes.length) {
                throw new Error('Malformed GIF sub-block sequence');
            }

            const length = bytes[pos++];

            if (length === 0) return pos;

            if (pos + length > bytes.length) {
                throw new Error('Truncated GIF sub-block');
            }

            pos += length;
        }
    }

    async function scrubGif(file) {
        if (file.size > MAX_FILE_BYTES) {
            throw new Error('GIF is too large');
        }

        const source = new Uint8Array(await file.arrayBuffer());

        if (source.length < 13) {
            throw new Error('GIF is too short');
        }

        const signature = ascii(source, 0, 6);

        if (signature !== 'GIF87a' && signature !== 'GIF89a') {
            throw new Error('Invalid GIF signature');
        }

        const chunks = [];
        let pos = 13;

        const packed = source[10];

        if ((packed & 0x80) !== 0) {
            const tableEntries = 1 << ((packed & 0x07) + 1);
            const tableBytes = 3 * tableEntries;

            if (pos + tableBytes > source.length) {
                throw new Error('Truncated GIF global color table');
            }

            pos += tableBytes;
        }

        chunks.push(source.slice(0, pos));

        let foundTrailer = false;

        while (pos < source.length) {
            const marker = source[pos];

            if (marker === 0x3B) {
                chunks.push(source.slice(pos, pos + 1));
                foundTrailer = true;
                break;
            }

            if (marker === 0x2C) {
                const start = pos;

                if (pos + 10 > source.length) {
                    throw new Error('Truncated GIF image descriptor');
                }

                const imagePacked = source[pos + 9];
                pos += 10;

                if ((imagePacked & 0x80) !== 0) {
                    const entries = 1 << ((imagePacked & 0x07) + 1);
                    const bytesNeeded = 3 * entries;

                    if (pos + bytesNeeded > source.length) {
                        throw new Error('Truncated GIF local color table');
                    }

                    pos += bytesNeeded;
                }

                if (pos >= source.length) {
                    throw new Error('Missing GIF LZW code size');
                }

                pos++;
                pos = endOfGifSubBlocks(source, pos);

                chunks.push(source.slice(start, pos));
                continue;
            }

            if (marker === 0x21) {
                if (pos + 2 > source.length) {
                    throw new Error('Truncated GIF extension');
                }

                const label = source[pos + 1];

                // Graphic Control Extension:
                // Keep frame delay, transparency and disposal.
                if (label === 0xF9) {
                    if (pos + 8 > source.length) {
                        throw new Error(
                            'Truncated GIF graphic control extension'
                        );
                    }

                    if (
                        source[pos + 2] !== 0x04 ||
                        source[pos + 7] !== 0x00
                    ) {
                        throw new Error(
                            'Malformed GIF graphic control extension'
                        );
                    }

                    chunks.push(source.slice(pos, pos + 8));
                    pos += 8;
                    continue;
                }

                // Comment Extension: discard.
                if (label === 0xFE) {
                    pos = endOfGifSubBlocks(source, pos + 2);
                    continue;
                }

                // Plain Text Extension: preserve.
                if (label === 0x01) {
                    const start = pos;

                    if (pos + 3 > source.length) {
                        throw new Error(
                            'Truncated GIF plain text extension'
                        );
                    }

                    const headerSize = source[pos + 2];

                    if (headerSize !== 12) {
                        throw new Error(
                            'Malformed GIF plain text extension'
                        );
                    }

                    pos += 3 + headerSize;
                    pos = endOfGifSubBlocks(source, pos);

                    chunks.push(source.slice(start, pos));
                    continue;
                }

                // Application Extension:
                // Only preserve standard animation loop data.
                if (label === 0xFF) {
                    const start = pos;

                    if (pos + 3 > source.length) {
                        throw new Error(
                            'Truncated GIF application extension'
                        );
                    }

                    const headerSize = source[pos + 2];

                    if (pos + 3 + headerSize > source.length) {
                        throw new Error(
                            'Truncated GIF application identifier'
                        );
                    }

                    let identifier = '';

                    if (headerSize === 11) {
                        identifier = ascii(source, pos + 3, 11);
                    }

                    pos += 3 + headerSize;
                    pos = endOfGifSubBlocks(source, pos);

                    if (
                        identifier === 'NETSCAPE2.0' ||
                        identifier === 'ANIMEXTS1.0'
                    ) {
                        chunks.push(source.slice(start, pos));
                    }

                    continue;
                }

                // Unknown extensions: discard.
                pos = endOfGifSubBlocks(source, pos + 2);
                continue;
            }

            throw new Error(
                `Unknown GIF block: 0x${marker.toString(16).padStart(2, '0')}`
            );
        }

        if (!foundTrailer) {
            throw new Error('GIF trailer not found');
        }

        const sanitized = concatChunks(chunks);

        return new File(
            [sanitized],
            randomFilename('.gif'),
            {
                type: 'image/gif',
                lastModified: Date.now()
            }
        );
    }

    // ============================================================
    // WebP RIFF helpers
    // ============================================================

    function parseWebPChunks(bytes) {
        if (bytes.length < 12) {
            throw new Error('WebP file is too short');
        }

        if (
            ascii(bytes, 0, 4) !== 'RIFF' ||
            ascii(bytes, 8, 4) !== 'WEBP'
        ) {
            throw new Error('Invalid WebP RIFF header');
        }

        const riffSize = readUint32LE(bytes, 4);
        const declaredEnd = riffSize + 8;

        if (declaredEnd > bytes.length) {
            throw new Error('Truncated WebP RIFF container');
        }

        const chunks = [];
        let pos = 12;

        while (pos < declaredEnd) {
            if (pos + 8 > declaredEnd) {
                throw new Error('Truncated WebP chunk header');
            }

            const fourCC = ascii(bytes, pos, 4);
            const size = readUint32LE(bytes, pos + 4);

            const payloadStart = pos + 8;
            const payloadEnd = payloadStart + size;
            const paddedEnd = payloadEnd + (size & 1);

            if (paddedEnd > declaredEnd) {
                throw new Error(`Truncated WebP chunk: ${fourCC}`);
            }

            chunks.push({
                fourCC,
                start: pos,
                payloadStart,
                payloadEnd,
                paddedEnd,
                size
            });

            pos = paddedEnd;
        }

        if (pos !== declaredEnd) {
            throw new Error('Malformed WebP RIFF size');
        }

        return chunks;
    }

    function webPHasAnimation(bytes, chunks) {
        const vp8x = chunks.find(
            chunk => chunk.fourCC === 'VP8X'
        );

        if (vp8x) {
            if (vp8x.size !== 10) {
                throw new Error('Malformed WebP VP8X chunk');
            }

            const flags = bytes[vp8x.payloadStart];

            if ((flags & 0x02) !== 0) {
                return true;
            }
        }

        return chunks.some(
            chunk =>
                chunk.fourCC === 'ANIM' ||
                chunk.fourCC === 'ANMF'
        );
    }

    // ============================================================
    // Animated WebP sanitizer
    //
    // Preserve: VP8X, ANIM, ANMF, ALPH, VP8, VP8L
    // Remove: EXIF, XMP, ICCP and unknown top-level chunks
    // ============================================================

    async function scrubAnimatedWebP(file, source, chunks) {
        const vp8x = chunks.find(
            chunk => chunk.fourCC === 'VP8X'
        );

        if (!vp8x) {
            throw new Error('Animated WebP has no VP8X chunk');
        }

        if (vp8x.size !== 10) {
            throw new Error('Malformed VP8X chunk');
        }

        const hasAnim = chunks.some(
            chunk => chunk.fourCC === 'ANIM'
        );

        const hasFrame = chunks.some(
            chunk => chunk.fourCC === 'ANMF'
        );

        if (!hasAnim || !hasFrame) {
            throw new Error('Malformed animated WebP');
        }

        const allowed = new Set([
            'VP8X', 'ANIM', 'ANMF',
            'ALPH', 'VP8 ', 'VP8L'
        ]);

        const header = source.slice(0, 12);
        const outputChunks = [header];

        for (const chunk of chunks) {
            if (
                chunk.fourCC === 'EXIF' ||
                chunk.fourCC === 'XMP ' ||
                chunk.fourCC === 'ICCP'
            ) {
                continue;
            }

            if (!allowed.has(chunk.fourCC)) {
                continue;
            }

            let copy = source.slice(
                chunk.start,
                chunk.paddedEnd
            );

            if (chunk.fourCC === 'VP8X') {
                copy = new Uint8Array(copy);

                // Clear ICC, EXIF and XMP feature flags.
                copy[8] &= ~(0x20 | 0x08 | 0x04);

                // Keep the animation feature flag enabled.
                copy[8] |= 0x02;
            }

            outputChunks.push(copy);
        }

        const sanitized = concatChunks(outputChunks);

        // Update RIFF size after metadata removal.
        writeUint32LE(
            sanitized,
            4,
            sanitized.length - 8
        );

        return new File(
            [sanitized],
            randomFilename('.webp'),
            {
                type: 'image/webp',
                lastModified: Date.now()
            }
        );
    }

    // ============================================================
    // Static image sanitizer
    // Decode and redraw pixels to strip embedded metadata
    // ============================================================

    async function decodeImage(file) {
        if (createImageBitmapSafe) {
            try {
                return await createImageBitmapSafe(
                    file,
                    { imageOrientation: 'from-image' }
                );
            } catch (_) {}
        }

        const objectURL = URL.createObjectURL(file);

        try {
            return await new Promise((resolve, reject) => {
                const image = new Image();

                image.onload = () => resolve(image);

                image.onerror = () => reject(
                    new Error('Image decode failed')
                );

                image.src = objectURL;
            });
        } finally {
            URL.revokeObjectURL(objectURL);
        }
    }

    function canvasToBlob(canvas, type, quality) {
        return new Promise((resolve, reject) => {
            canvas.toBlob(
                blob => {
                    if (!blob) {
                        reject(new Error('canvas.toBlob failed'));
                        return;
                    }

                    resolve(blob);
                },
                type,
                quality
            );
        });
    }

    async function scrubRasterImage(file, sourceMime) {
        if (file.size > MAX_FILE_BYTES) {
            throw new Error('Image file is too large');
        }

        let outputMime;

        if (sourceMime === 'image/webp') {
            outputMime = 'image/webp';
        } else if (CANVAS_SAME_FORMAT.has(sourceMime)) {
            outputMime = sourceMime;
        } else if (CONVERT_TO_PNG.has(sourceMime)) {
            outputMime = 'image/png';
        } else {
            throw new Error(
                `Unsupported image type: ${sourceMime}`
            );
        }

        const decoded = await decodeImage(file);

        try {
            const width =
                Number(decoded.width) ||
                Number(decoded.naturalWidth);

            const height =
                Number(decoded.height) ||
                Number(decoded.naturalHeight);

            if (
                !Number.isFinite(width) ||
                !Number.isFinite(height) ||
                width <= 0 ||
                height <= 0
            ) {
                throw new Error('Invalid image dimensions');
            }

            if (width * height > MAX_PIXELS) {
                throw new Error('Image exceeds pixel safety limit');
            }

            const canvas = document.createElement('canvas');

            canvas.width = width;
            canvas.height = height;

            const context = canvas.getContext(
                '2d',
                { alpha: outputMime !== 'image/jpeg' }
            );

            if (!context) {
                throw new Error('Canvas context unavailable');
            }

            if (outputMime === 'image/jpeg') {
                context.fillStyle = '#ffffff';
                context.fillRect(0, 0, width, height);
            }

            context.drawImage(
                decoded,
                0,
                0,
                width,
                height
            );

            const quality =
                outputMime === 'image/jpeg' ||
                outputMime === 'image/webp'
                    ? 0.98
                    : undefined;

            const blob = await canvasToBlob(
                canvas,
                outputMime,
                quality
            );

            const actualMime = String(
                blob.type || ''
            ).toLowerCase();

            if (!new Set([
                'image/png',
                'image/jpeg',
                'image/webp'
            ]).has(actualMime)) {
                throw new Error(
                    `Unexpected encoder output: ${actualMime}`
                );
            }

            return new File(
                [blob],
                randomFilename(
                    extensionForMime(actualMime)
                ),
                {
                    type: actualMime,
                    lastModified: Date.now()
                }
            );
        } finally {
            if (
                decoded &&
                typeof decoded.close === 'function'
            ) {
                decoded.close();
            }
        }
    }

    async function scrubWebP(file) {
        if (file.size > MAX_FILE_BYTES) {
            throw new Error('WebP file is too large');
        }

        const source = new Uint8Array(
            await file.arrayBuffer()
        );

        const chunks = parseWebPChunks(source);

        if (webPHasAnimation(source, chunks)) {
            return await scrubAnimatedWebP(
                file,
                source,
                chunks
            );
        }

        return await scrubRasterImage(
            file,
            'image/webp'
        );
    }

    async function scrubImage(file) {
        const mime = inferMime(file);

        if (!mime) {
            throw new Error('Unknown image format');
        }

        if (mime === 'image/gif') {
            return await scrubGif(file);
        }

        if (mime === 'image/webp') {
            return await scrubWebP(file);
        }

        if (mime === 'image/svg+xml') {
            throw new Error('SVG upload blocked');
        }

        return await scrubRasterImage(file, mime);
    }

    async function processSelection(files) {
        const output = [];

        for (const file of files) {
            if (isImageCandidate(file)) {
                output.push(await scrubImage(file));
            } else {
                output.push(file);
            }
        }

        return output;
    }

    // ============================================================
    // File input interception
    // Process files before the website handles them
    // ============================================================

    function stopOriginalEvent(event) {
        try {
            event.preventDefault();
        } catch (_) {}

        try {
            event.stopImmediatePropagation();
        } catch (_) {}

        try {
            event.stopPropagation();
        } catch (_) {}
    }

    function clearFileInput(input) {
        try {
            input.value = '';
        } catch (_) {}

        try {
            const transfer = new DataTransfer();
            input.files = transfer.files;
        } catch (_) {}
    }

    function dispatchSanitizedEvents(input) {
        const inputEvent = new Event(
            'input',
            {
                bubbles: true,
                cancelable: false
            }
        );

        const changeEvent = new Event(
            'change',
            {
                bubbles: true,
                cancelable: false
            }
        );

        syntheticEvents.add(inputEvent);
        syntheticEvents.add(changeEvent);

        input.dispatchEvent(inputEvent);
        input.dispatchEvent(changeEvent);
    }

    function handleFileInputEvent(event) {
        if (syntheticEvents.has(event)) {
            return;
        }

        const input = event.target;

        if (
            !input ||
            input.nodeType !== 1 ||
            input.tagName !== 'INPUT' ||
            String(input.type).toLowerCase() !== 'file'
        ) {
            return;
        }

        const existingState = inputStates.get(input);

        if (
            event.type === 'change' &&
            existingState?.blockNativeChange
        ) {
            stopOriginalEvent(event);

            existingState.blockNativeChange = false;
            return;
        }

        const files = Array.from(input.files || []);

        if (!files.some(isImageCandidate)) {
            return;
        }

        stopOriginalEvent(event);

        const generation =
            (existingState?.generation || 0) + 1;

        inputStates.set(input, {
            generation,
            blockNativeChange: event.type === 'input'
        });

        clearFileInput(input);

        void (async () => {
            try {
                const processed = await processSelection(files);

                const current = inputStates.get(input);

                if (
                    !current ||
                    current.generation !== generation
                ) {
                    return;
                }

                const transfer = new DataTransfer();

                for (const file of processed) {
                    transfer.items.add(file);
                }

                input.files = transfer.files;

                dispatchSanitizedEvents(input);
            } catch (_) {
                clearFileInput(input);

                notifyFailure(
                    '이미지 개인정보 제거에 실패하여 업로드를 차단했습니다.'
                );
            }
        })();
    }

    window.addEventListener(
        'input',
        handleFileInputEvent,
        true
    );

    window.addEventListener(
        'change',
        handleFileInputEvent,
        true
    );

    // ============================================================
    // Drag/drop and paste protection
    // Block image uploads through unsupported transfer paths
    // ============================================================

    function transferContainsImage(event) {
        const transfer =
            event.dataTransfer ||
            event.clipboardData;

        if (!transfer) {
            return false;
        }

        try {
            for (const file of Array.from(transfer.files || [])) {
                if (isImageCandidate(file)) {
                    return true;
                }
            }
        } catch (_) {}

        try {
            for (const item of Array.from(transfer.items || [])) {
                if (item.kind !== 'file') {
                    continue;
                }

                const type = String(
                    item.type || ''
                ).toLowerCase();

                if (!type || type.startsWith('image/')) {
                    return true;
                }
            }
        } catch (_) {}

        try {
            const types = Array.from(transfer.types || []);

            if (
                event.type !== 'paste' &&
                types.includes('Files')
            ) {
                return true;
            }
        } catch (_) {}

        return false;
    }

    function blockTransferEvent(event) {
        if (!transferContainsImage(event)) {
            return;
        }

        stopOriginalEvent(event);

        if (
            event.type === 'drop' ||
            event.type === 'paste'
        ) {
            notifyFailure(
                '이미지 드래그/붙여넣기는 개인정보 보호를 위해 차단했습니다. 파일 선택 버튼을 사용하세요.'
            );
        }
    }

    window.addEventListener(
        'dragenter',
        blockTransferEvent,
        true
    );

    window.addEventListener(
        'dragover',
        blockTransferEvent,
        true
    );

    window.addEventListener(
        'drop',
        blockTransferEvent,
        true
    );

    window.addEventListener(
        'paste',
        blockTransferEvent,
        true
    );
})();
