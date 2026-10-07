#!/usr/bin/env python3
"""Optional browser smoke test for the bundled explorer (requires Playwright).

Example: python tools/tests/check_proof_explorer_browser.py --browser-channel msedge
Uses a local file, without a server or external requests. Screenshots and a
machine-readable report go to the chosen output directory.
"""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    from playwright.sync_api import sync_playwright

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--browser-channel', default=None)
    parser.add_argument('--output', type=Path, default=ROOT / 'tmp/explorer-browser')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    uri = (ROOT / 'docs/explorer/index.html').as_uri()
    checks, errors, external_requests = [], [], []

    def check(condition, name):
        if not condition:
            raise AssertionError(name)
        checks.append(name)

    with sync_playwright() as p:
        launch = {'headless': True}
        if args.browser_channel:
            launch['channel'] = args.browser_channel
        browser = p.chromium.launch(**launch)
        context = browser.new_context(viewport={'width':1440, 'height':1100})
        context.on('request', lambda r: external_requests.append(r.url) if r.url.startswith(('http:', 'https:')) else None)
        page = context.new_page()
        page.on('pageerror', lambda error: errors.append(str(error)))
        page.goto(uri)
        page.wait_for_function('window.SSLPExplorer !== undefined')
        state = lambda: page.evaluate('SSLPExplorer.getState()')
        rows = lambda: page.evaluate('SSLPExplorer.getResults()')
        check(page.locator('#module-count').inner_text() == '16,227', 'complete source count')
        check('Orbit2FullImage' in page.locator('#detail').inner_text(), 'default full-image endpoint')
        check('MainTheory.Orbit2FullImage.directory_image' in page.locator('#detail').inner_text(), 'actual orbit-2 declaration')
        check('5 held main-text issues' in page.locator('#detail').inner_text(), 'held manuscript scope remains visible')
        check(page.locator('.proof-card').count() == 24, 'initial result pagination')
        page.locator('#load-more').click()
        check(page.locator('.proof-card').count() == 48, 'load more results')
        page.locator('#reset').click()
        page.screenshot(path=str(args.output / 'desktop-dark.png'), animations='disabled')
        page.locator('#theme-toggle').click()
        check(page.locator('html').get_attribute('data-theme') == 'light', 'light theme')
        page.screenshot(path=str(args.output / 'desktop-light.png'), animations='disabled')
        page.locator('#theme-toggle').click()
        page.locator('#search').fill('orbit 2')
        check(bool(rows()) and all(2 in r['orbits'] for r in rows()), 'orbit 2 exact token excludes orbit 20')
        page.locator('#search').fill('orbit3')
        check(bool(rows()) and all(3 in r['orbits'] for r in rows()), 'orbit3 compact token')
        check('MainTheory.Orbit3FullImage.directory_image' in page.locator('#detail').inner_text(), 'orbit-3 endpoint resources')
        page.locator('#reset').click()
        page.locator('#modules-tab').click()
        check(len(rows()) == 1779, 'generated shards initially hidden')
        page.locator('#generated').check()
        check(len(rows()) == 16227, 'all active modules available')
        page.locator('#search').fill('MainTheory.Orbit3FullImage')
        check(len(rows()) == 1 and rows()[0]['paths'] == ['MainTheory/Orbit3FullImage.lean'], 'qualified module search')
        page.locator('.skip').focus()
        page.keyboard.press('Enter')
        check(state()['q'] == 'MainTheory.Orbit3FullImage' and page.locator('#search').evaluate('(e)=>document.activeElement===e'), 'skip link preserves filters')
        page.locator('#detail .copy-button').click()
        page.locator('#toast').wait_for(state='visible')
        check('Copied' in page.locator('#toast').inner_text() or 'Clipboard unavailable' in page.locator('#toast').inner_text(), 'clipboard feedback')
        saved_url = page.url
        second = context.new_page()
        second.on('pageerror', lambda error: errors.append(str(error)))
        second.goto(saved_url)
        second.wait_for_function('window.SSLPExplorer !== undefined')
        check(second.evaluate('SSLPExplorer.getState().q') == 'MainTheory.Orbit3FullImage', 'URL state restoration')
        second.close()
        page.locator('#reset').click()
        page.locator('[data-library="QECC"]').click()
        check(len(rows()) == 52 and all(r['paths'][0] == 'QECC.lean' or r['paths'][0].startswith('QECC/') for r in rows()), 'library filtering')
        topics = page.locator('#topic-select option').evaluate_all('(options)=>options.map(o=>o.value).filter(Boolean)')
        topic = next(t for t in topics if page.evaluate('(t)=>JSON.parse(document.getElementById("proof-data").textContent).topics.includes(t)', t) and page.evaluate('(t)=>{const d=JSON.parse(document.getElementById("proof-data").textContent);return d.modules.some(m=>d.libraries[m[1]]==="QECC"&&d.topics[m[2]]===t)}', t))
        page.locator('#topic-select').select_option(topic)
        check(0 < len(rows()) <= 52 and state()['library'] == 'QECC', 'combined library and topic filters')
        page.locator('#reset').click()
        page.locator('#orbit-select').select_option('2')
        check(bool(rows()) and all(2 in r['orbits'] for r in rows()), 'orbit dropdown')
        page.locator('#search').fill('thisdoesnotexist')
        check(not rows() and page.locator('.empty').is_visible(), 'empty state')
        page.locator('#reset').click()
        page.locator('#guides-tab').focus()
        page.keyboard.press('ArrowRight')
        check(state()['mode'] == 'modules', 'keyboard tab navigation')
        page.locator('#reset').focus()
        page.keyboard.press('/')
        check(page.locator('#search').evaluate('(e)=>document.activeElement===e'), 'keyboard search shortcut')
        page.locator('#guides-tab').click()
        page.locator('#reset').click()
        for width in (1440, 1280, 1024, 768, 390, 320):
            page.set_viewport_size({'width':width, 'height':1000})
            check(page.evaluate('document.documentElement.scrollWidth <= innerWidth'), f'no horizontal overflow at {width}px')
        page.set_viewport_size({'width':390, 'height':844})
        page.locator('#toast').wait_for(state='hidden')
        page.screenshot(path=str(args.output / 'mobile-dark.png'))
        page.locator('.proof-card').first.click()
        check(page.locator('#detail-dialog').evaluate('(e)=>e.open'), 'mobile detail dialog')
        check('MainTheory.Orbit2FullImage.directory_image' in page.locator('#dialog-content').inner_text(), 'mobile endpoint detail')
        page.screenshot(path=str(args.output / 'mobile-detail.png'))
        page.keyboard.press('Escape')
        check(not page.locator('#detail-dialog').evaluate('(e)=>e.open'), 'Escape closes dialog')
        check(page.evaluate('document.activeElement.classList.contains("proof-card")'), 'focus restored after dialog')
        context.close()
        browser.close()
    check(not errors, 'no JavaScript errors')
    check(not external_requests, 'offline page makes zero external requests')
    report = {'checks':checks, 'passed':len(checks), 'javascript_errors':errors, 'external_requests':external_requests,
              'viewports':[1440,1280,1024,768,390,320], 'browser_channel':args.browser_channel or 'chromium'}
    (args.output / 'browser-check.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: {len(checks)} browser checks; zero external requests and JavaScript errors')


if __name__ == '__main__':
    main()
