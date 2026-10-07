#!/usr/bin/env python3
"""Render the native banner timeline to a GitHub-compatible looping GIF.

Optional design dependencies: Pillow and Playwright, plus a local browser.
Run `python tools/render_banner.py --browser-channel msedge` on Windows,
or omit the channel after installing Playwright's Chromium browser.
The mathematical proof and verification tools do not depend on this renderer.
"""
import argparse
from io import BytesIO
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--browser-channel', help='Installed Playwright browser channel, e.g. msedge')
    parser.add_argument('--output', type=Path, default=ROOT / 'docs/assets/banner.gif')
    args = parser.parse_args(argv)
    from PIL import Image
    from playwright.sync_api import sync_playwright

    frames = []
    with sync_playwright() as playwright:
        browser = playwright.chromium.launch(channel=args.browser_channel, headless=True)
        page = browser.new_page(viewport={'width': 1200, 'height': 340}, device_scale_factor=1)
        svg = (ROOT / 'docs/assets/banner-motion.svg').read_text(encoding='utf-8')
        page.set_content('<!doctype html><html><head><style>body{margin:0}svg{display:block}</style></head><body>' + svg + '</body></html>')
        page.evaluate('document.querySelector("svg").pauseAnimations()')
        for index in range(120):
            page.evaluate('(t)=>document.querySelector("svg").setCurrentTime(t)', index * .15)
            frames.append(Image.open(BytesIO(page.screenshot(omit_background=True))).convert('RGBA'))
        browser.close()

    # One palette for the entire loop keeps the stationary typography stable.
    samples = Image.new('RGB', (300, 85 * 8), (9, 20, 37))
    for row, frame in enumerate(frames[::15]):
        sample = Image.new('RGB', frame.size, (9, 20, 37))
        sample.paste(frame, mask=frame.getchannel('A'))
        samples.paste(sample.resize((300, 85)), (0, row * 85))
    # Reserve the vector artwork's accent colors; sparse bright orbit strokes
    # otherwise lose out to the large dark background in GIF quantization.
    extra = {tuple(bytes.fromhex(color[1:])) for color in re.findall(r'#[0-9a-fA-F]{6}', svg)}
    teal, purple = (104, 228, 217), (173, 156, 255)
    extra.update(tuple(round(a + (b - a) * i / 31) for a, b in zip(teal, purple)) for i in range(32))
    assert len(extra) <= 100
    background_colors = 255 - len(extra)
    palette = samples.quantize(colors=background_colors)
    colors = palette.getpalette()[:background_colors * 3]
    colors += [channel for color in sorted(extra) for channel in color]
    palette.putpalette(colors + [0, 0, 0])
    encoded = []
    for frame in frames:
        rgb = Image.new('RGB', frame.size, (9, 20, 37))
        rgb.paste(frame, mask=frame.getchannel('A'))
        image = rgb.quantize(palette=palette, dither=Image.Dither.NONE)
        image.paste(255, mask=frame.getchannel('A').point(lambda a: 255 if a < 128 else 0))
        encoded.append(image)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    encoded[0].save(args.output, save_all=True, append_images=encoded[1:],
                    duration=150, loop=0, transparency=255, disposal=1, optimize=True)
    with Image.open(args.output) as check:
        assert check.size == (1200, 340) and check.n_frames == 120
        assert check.info['loop'] == 0
        check.seek(30)
        quarter = check.convert('RGBA')
        check.seek(0)
        first = check.convert('RGBA')
        assert first.crop((0, 0, 620, 340)).tobytes() == quarter.crop((0, 0, 620, 340)).tobytes()
        assert first.tobytes() != quarter.tobytes()
    print(f'PASS: {args.output.name}, 120 frames, 18-second seamless loop, {args.output.stat().st_size:,} bytes; text stays fixed')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
