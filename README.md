Source for www.brendan.phd, served by GitHub Pages from the committed files.

The homepage is `src/index.md`, rendered by pandoc with the template and CSS
from <https://github.com/jez/pandoc-markdown-css-theme>. After editing it, run

    nix run .#build

to regenerate `index.html`. `nix flake check` fails if `index.html` is stale.
