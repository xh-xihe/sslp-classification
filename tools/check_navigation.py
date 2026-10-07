#!/usr/bin/env python3
"""Check curated repository links, Markdown anchors and self-contained SVGs.

Uses only the standard library and makes no network requests. Historical notes
and acceptance records are not rewritten or interpreted as current navigation.
This is a presentation check, not a Lean or manuscript certification gate.
"""
import argparse
from html import unescape
from html.parser import HTMLParser
from pathlib import Path
import re
import unicodedata
from urllib.parse import unquote, urlsplit
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
CORE = ('README.md', 'REPRODUCE.md', 'HISTORY.md', 'CONTRIBUTING.md',
        'tools/README.md', '.github/pull_request_template.md', 'docs/assets/README.md')


def prose(text):
    """Exclude fenced/indented code, inline code and comments from link checks."""
    lines, fence = [], None
    for line in text.splitlines():
        marker = re.match(r'^\s{0,3}(`{3,}|~{3,})', line)
        if marker:
            token = marker[1]
            if fence is None:
                fence = token
            elif token[0] == fence[0] and len(token) >= len(fence):
                fence = None
            continue
        if fence is None and not line.startswith(('    ', '\t')):
            lines.append(line)
    text = re.sub(r'<!--.*?-->', '', '\n'.join(lines), flags=re.S)
    return re.sub(r'(`+).*?\1', '', text)


class Attributes(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.links, self.ids = [], set()

    def handle_starttag(self, tag, attrs):
        for name, value in attrs:
            if value is None:
                continue
            if name in ('href', 'src'):
                self.links.append(value)
            elif name == 'srcset':
                self.links.extend(item.strip().split()[0] for item in value.split(',') if item.strip())
            elif name == 'id' or (tag == 'a' and name == 'name'):
                self.ids.add(value)

    handle_startendtag = handle_starttag


def links(text):
    text = prose(text)
    parser = Attributes()
    parser.feed(text)
    found = list(parser.links)
    # Inline Markdown links/images; optional title is excluded from the target.
    found += re.findall(r'!?\[[^\]\n]*\]\(\s*<?([^\s<>]+?)>?(?:\s+["\'][^\n]*?["\'])?\s*\)', text)
    # Reference definitions are checked even if they are currently unused.
    found += re.findall(r'^\s{0,3}\[[^\]\n]+\]:\s*<?([^\s<>]+)>?', text, re.M)
    return found


def anchors(text):
    # Retain inline code in headings: its visible content belongs to the slug.
    clean = re.sub(r'<!--.*?-->', '', text, flags=re.S)
    clean = re.sub(r'^\s{0,3}(`{3,}|~{3,}).*?^\s{0,3}\1\s*$', '', clean, flags=re.M | re.S)
    parser = Attributes()
    parser.feed(clean)
    result, used = set(parser.ids), set()
    for heading in re.findall(r'^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$', clean, re.M):
        heading = re.sub(r'<[^>]+>', '', heading)
        heading = re.sub(r'!?\[([^\]]+)\]\([^)]*\)', r'\1', heading)
        heading = unescape(heading).lower()
        slug = ''.join(c for c in heading if c in '-_' or not unicodedata.category(c).startswith(('P', 'S')))
        slug = slug.replace(' ', '-')
        unique, index = slug, 0
        while unique in used:
            index += 1
            unique = f'{slug}-{index}'
        used.add(unique)
        result.add(unique)
    return result


def check_links(root, documents):
    root = Path(root).resolve()
    errors, checked, anchor_cache = [], 0, {}
    for relative in documents:
        source = root / relative
        if not source.is_file():
            errors.append(f'{relative}: missing navigation document')
            continue
        for target in links(source.read_text(encoding='utf-8')):
            parsed = urlsplit(unescape(target))
            if parsed.scheme in ('https', 'http', 'mailto') or parsed.netloc:
                continue
            checked += 1
            if parsed.scheme:
                errors.append(f'{relative}: unsupported local link {target}')
                continue
            raw = unquote(parsed.path)
            destination = ((root if raw.startswith('/') else source.parent) / raw.lstrip('/')).resolve() if raw else source
            if not destination.is_relative_to(root):
                errors.append(f'{relative}: link escapes repository: {target}')
            elif not destination.exists():
                errors.append(f'{relative}: missing target: {target}')
            elif parsed.fragment and destination.suffix.lower() == '.md':
                if destination not in anchor_cache:
                    anchor_cache[destination] = anchors(destination.read_text(encoding='utf-8'))
                if unquote(parsed.fragment) not in anchor_cache[destination]:
                    errors.append(f'{relative}: missing anchor: {target}')
    return checked, errors


def check_svgs(root):
    errors, count = [], 0
    for path in sorted((Path(root) / 'docs/assets').glob('*.svg')):
        count += 1
        try:
            tree = ET.fromstring(path.read_bytes())
        except ET.ParseError as exc:
            errors.append(f'{path.name}: invalid SVG: {exc}')
            continue
        if tree.tag != '{http://www.w3.org/2000/svg}svg' or 'viewBox' not in tree.attrib:
            errors.append(f'{path.name}: expected SVG root with viewBox')
        if not any(node.tag.endswith('}title') and node.text for node in tree):
            errors.append(f'{path.name}: missing accessible title')
        for node in tree.iter():
            if node.tag.rsplit('}', 1)[-1] in ('script', 'foreignObject'):
                errors.append(f'{path.name}: active embedded content')
            for key, value in node.attrib.items():
                if key.lower().startswith('on'):
                    errors.append(f'{path.name}: event handler')
                if key.rsplit('}', 1)[-1] in ('href', 'src') and not value.startswith('#'):
                    errors.append(f'{path.name}: external resource')
                if re.search(r'url\(\s*["\']?(?!#)[^\s"\')]', value):
                    errors.append(f'{path.name}: nonlocal CSS resource')
    if not count:
        errors.append('docs/assets: no SVG assets to check')
    return count, errors


def gif_info(data):
    """Inspect GIF blocks without Pillow; reject missing/truncated payloads."""
    if len(data) < 14 or data[:6] not in (b'GIF87a', b'GIF89a'):
        raise ValueError('invalid GIF header')
    width = int.from_bytes(data[6:8], 'little')
    height = int.from_bytes(data[8:10], 'little')
    if not width or not height:
        raise ValueError('empty canvas')
    position = 13
    if data[10] & 128:
        position += 3 * (2 << (data[10] & 7))
    frames, duration, loop = 0, 0, None

    def take(count):
        nonlocal position
        if position + count > len(data):
            raise ValueError('truncated GIF block')
        chunk = data[position:position + count]
        position += count
        return chunk

    def blocks():
        result = b''
        while True:
            count = take(1)[0]
            if not count:
                return result
            result += take(count)

    while True:
        token = take(1)[0]
        if token == 0x3b:
            if position != len(data):
                raise ValueError('unexpected data after GIF trailer')
            break
        if token == 0x21:
            label = take(1)[0]
            content = blocks()
            if label == 0xf9:
                if len(content) != 4:
                    raise ValueError('invalid graphics control block')
                duration += int.from_bytes(content[1:3], 'little') * 10
            elif label == 0xff and content.startswith(b'NETSCAPE2.0\x01'):
                loop = int.from_bytes(content[12:14], 'little')
        elif token == 0x2c:
            descriptor = take(9)
            left, top, frame_width, frame_height = [int.from_bytes(descriptor[i:i + 2], 'little') for i in (0, 2, 4, 6)]
            if not frame_width or not frame_height or left + frame_width > width or top + frame_height > height:
                raise ValueError('frame outside GIF canvas')
            if descriptor[8] & 128:
                take(3 * (2 << (descriptor[8] & 7)))
            code_size = take(1)[0]
            if not 2 <= code_size <= 8 or not blocks():
                raise ValueError('invalid image data block')
            frames += 1
        else:
            raise ValueError('unknown GIF block')
    if frames < 2 or duration <= 0:
        raise ValueError('expected timed animation with multiple frames')
    return {'width': width, 'height': height, 'frames': frames, 'duration_ms': duration, 'loop': loop}


def check_gifs(root):
    errors, count = [], 0
    for path in sorted((Path(root) / 'docs/assets').glob('*.gif')):
        count += 1
        try:
            info = gif_info(path.read_bytes())
            if info['loop'] != 0:
                errors.append(f'{path.name}: expected continuous loop')
        except ValueError as exc:
            errors.append(f'{path.name}: {exc}')
    return count, errors


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    args = parser.parse_args(argv)
    documents = list(CORE) + [p.relative_to(args.root).as_posix() for p in sorted((args.root / 'docs').glob('*.md'))]
    count, errors = check_links(args.root, documents)
    svg_count, svg_errors = check_svgs(args.root)
    gif_count, gif_errors = check_gifs(args.root)
    errors += svg_errors + gif_errors
    if errors:
        for error in errors:
            print('FAIL: ' + error)
        return 1
    print(f'PASS: {len(documents)} navigation documents, {count} local links/anchors, {svg_count} SVG assets, {gif_count} looping GIF assets')
    print('Scope: documentation only; external URLs, Lean proofs and manuscript correspondence are not checked.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
