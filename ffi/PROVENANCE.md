# Theme provenance

Vendored, not a submodule. `forester init` sets the theme up as a git
submodule pointing at sourcehut; that makes every clone of this repo
depend on sr.ht being up and on network access at the wrong moment, to
render a static site that is otherwise entirely offline. The files are
copied in instead.

    upstream  https://git.sr.ht/~jonsterling/forester-base-theme
    tag       5.0
    commit    23017d9c49e7685e9ec5949378f9b5e3cb924b58
    vendored  2026-08-23
    licence   see LICENSES/ -- the theme is MIT, the fonts and KaTeX
              carry their own (OFL, MIT)

`forester.js` is a minified bundle of KaTeX and ninja-keys. It is
checked in because the site must render offline, and it is rebuildable
from what is here: `./bundle-js.sh` runs esbuild over
`javascript-source/` against the pinned `package-lock.json`. Nothing
in the built site fetches from a CDN.

Verified: at tag 5.0 every file here is byte-identical to the theme
shipped inside forester 5.0 itself (`bin/forester/theme/` at rev
5ab7277c), so this is the version the binary was built against.

## Local changes

Exactly one file is ours, `default.xsl`, and one upstream file is
renamed. Forester 5.0 hardcodes the stylesheet name (`Forester.ml`
emits `<?xml-stylesheet href="/default.xsl"?>`; the 4.x
`forest.toml` `stylesheet` key no longer exists), so ours has to take
that name and upstream's is vendored as `base.xsl` -- same bytes, new
filename -- which ours imports. Every other file is untouched, so
re-vendoring a later tag is a clean overwrite and `git diff` shows
exactly what is ours.
