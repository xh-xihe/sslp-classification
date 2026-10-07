#!/usr/bin/env python3
"""Open the bundled proof explorer locally; no server or extra packages needed."""
from pathlib import Path
import webbrowser


def main():
    path = Path(__file__).resolve().parents[1] / 'docs/explorer/index.html'
    if not path.is_file():
        raise SystemExit('Build the explorer first: python tools/build_explorer.py')
    print('Opening SSLP Proof Explorer: ' + str(path))
    if not webbrowser.open(path.as_uri()):
        print('Open this file directly in a browser: ' + str(path))


if __name__ == '__main__':
    main()
