{
  description = "www.brendan.phd";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/e158d9ed9b51c98974c5e66e1ba1c9e0255fecaa";

  outputs = { self, nixpkgs }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "x86_64-darwin" "aarch64-darwin" ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});

      # The homepage, rendered from src/index.md. GitHub Pages serves the
      # committed index.html, so `nix run .#build` copies this into the
      # worktree and `nix flake check` fails when the two disagree.
      homepage = pkgs: pkgs.runCommand "brendan-phd-index" {
        nativeBuildInputs = [ pkgs.pandoc ];
        src = ./src/index.md;
        template = ./template.html5;
      } ''
        mkdir -p $out
        pandoc \
          --katex \
          --from markdown+tex_math_single_backslash \
          --to html5+smart \
          --template="$template" \
          --css=public/css/theme.css \
          --css=public/css/skylighting-solarized-theme.css \
          --toc \
          --output $out/index.html \
          "$src"
      '';

      # pdfs/Spectra.pdf, typeset from notes/spectra. SOURCE_DATE_EPOCH and
      # FORCE_SOURCE_DATE pin the timestamps pdfTeX writes, so the output is
      # byte-for-byte reproducible and can be checked like index.html.
      spectraNotes = pkgs:
        let
          tex = pkgs.texliveSmall.withPackages (ps: with ps; [ tikz-cd pgf microtype lm ]);
        in
        pkgs.runCommand "spectra-notes" {
          nativeBuildInputs = [ tex ];
          src = ./notes/spectra;
          SOURCE_DATE_EPOCH = "1707782400"; # 2024-02-13, when the notes were written
          FORCE_SOURCE_DATE = "1";
        } ''
          cp -r "$src"/. .
          chmod -R u+w .
          export HOME=$TMPDIR
          pdflatex -interaction=nonstopmode -halt-on-error spectra.tex
          pdflatex -interaction=nonstopmode -halt-on-error spectra.tex
          if grep -E '^(LaTeX|Package) .*Warning|Undefined control sequence|Overfull' spectra.log; then
            echo "spectra.tex has warnings; see above" >&2
            exit 1
          fi
          mkdir -p $out
          cp spectra.pdf $out/Spectra.pdf
        '';
    in
    {
      packages = forAllSystems (pkgs: {
        default = homepage pkgs;
        spectra-notes = spectraNotes pkgs;
      });

      apps = forAllSystems (pkgs: {
        build = {
          type = "app";
          program = toString (pkgs.writeShellScript "build-site" ''
            set -euo pipefail
            if [ ! -f CNAME ] || [ ! -f src/index.md ]; then
              echo "run this from the root of the website repository" >&2
              exit 1
            fi
            install -m 0644 ${homepage pkgs}/index.html index.html
            install -m 0644 ${spectraNotes pkgs}/Spectra.pdf pdfs/Spectra.pdf
          '');
        };
      });

      checks = forAllSystems (pkgs: {
        index-up-to-date = pkgs.runCommand "index-up-to-date" { } ''
          if ! diff -u ${./index.html} ${homepage pkgs}/index.html; then
            echo "index.html is stale; run: nix run .#build" >&2
            exit 1
          fi
          touch $out
        '';
        spectra-up-to-date = pkgs.runCommand "spectra-up-to-date" { } ''
          if ! cmp ${./pdfs/Spectra.pdf} ${spectraNotes pkgs}/Spectra.pdf; then
            echo "pdfs/Spectra.pdf is stale; run: nix run .#build" >&2
            exit 1
          fi
          touch $out
        '';
      });
    };
}
