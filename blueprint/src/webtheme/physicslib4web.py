"""
plasTeX package physicslib4web: the physicslib4 website's header and theme on the web blueprint.

Loaded by `\\usepackage{physicslib4web}` in `web.tex`, after the `blueprint` package, and found
through `packages-dirs` in `plastex.cfg`. It is used by the web version only; `print.tex` does
not load it, so the PDF is unaffected.

- `templates/` holds the page layouts (`default-layout.jinja2` for the chapter pages,
  `document-layout.jinja2` for the title page). They are plasTeX's default-theme layouts with the
  header replaced by the website header and with the fonts, icon and theme script of the
  website in the head. Package template directories are loaded after the theme, so these
  layouts take the place of the theme's.
- `site-header.html` is the header, kept in `rendererdata['html5']['site_header']`, from where
  the two layouts and the dependency graph template (`dep_graph.html`, selected by the
  `tpl=` option of the `blueprint` package in `web.tex`) insert it.
- `physicslib4-theme.js` switches between the light and dark theme, as on the website.

The look itself (fonts, colours, header measurements, theorem boxes, table of contents,
dependency graph page) is in `extra_styles.css`, the stylesheet named by `extra-css` in
`plastex.cfg`.
"""
from pathlib import Path

from plasTeX.PackageResource import PackageJs, PackageTemplateDir

PKG_DIR = Path(__file__).parent


def ProcessOptions(options, document):
    """Register the layouts, the header and the theme script."""
    rendererdata = document.rendererdata.setdefault('html5', dict())
    rendererdata['site_header'] = (PKG_DIR/'site-header.html').read_text(encoding='utf-8')
    document.addPackageResource([
        PackageTemplateDir(path=PKG_DIR/'templates'),
        # Copied to js/ only: the layouts load it in the head, before the page is drawn.
        PackageJs(path=PKG_DIR/'physicslib4-theme.js', copy_only=True),
    ])
