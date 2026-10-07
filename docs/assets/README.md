# Presentation assets

The banner and proof map are original repository artwork, built from vector
source. The orbit motif is decorative; mathematical content is supplied by
the linked Lean statements and version-bound review records.

- `banner.svg`: static banner and reduced-motion fallback.
- `banner-motion.svg`: native 18-second animation timeline.
- `banner.gif`: rendered loop used in the repository README.
- `proof-map.svg`: graphical reading map; destinations are linked in
  [the proof-map guide](../proof-map.md).
- `lean.svg`, `mathlib.svg`, `kernel.svg`, `review.svg`: local version/scope badges.
- `explorer-preview.png`: desktop screenshot of the bundled
  [interactive proof explorer](../explorer.md).

The homepage uses a `picture` element to select the static banner when the
browser requests reduced motion. A static image is also available directly
as `banner.svg`.

To regenerate the GIF, install Pillow and Playwright in a design environment,
then run from the repository root:

```console
python tools/render_banner.py --browser-channel msedge
```

With Playwright's Chromium installed, omit `--browser-channel msedge`.
The renderer samples the vector timeline with a common palette, retains
transparent corners, and keeps the title fixed throughout the loop. Its
dependencies are separate from mathematical proof verification.

The explorer screenshot comes from the optional browser smoke check documented
in [the explorer guide](../explorer.md#maintain-the-explorer).
