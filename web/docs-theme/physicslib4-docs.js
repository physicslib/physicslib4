// Keeps doc-gen4's colour scheme in step with the physicslib4 theme on the API docs.
//
// The site's theme script (physicslib4-theme.js, loaded just before this one) puts the class
// `light-theme` or `dark-theme` on <html> and stores the reader's choice under the website's
// `localStorage` keys. doc-gen4 keys its own colours on the attribute `data-theme` of <html>, set
// by its color-scheme.js (in the module-list frame, navbar.html) from `localStorage.theme`. This
// script makes the site's class the one source: whenever it changes, `data-theme`, the key `theme`
// and the module-list frame follow. doc-gen4's own picker at the foot of the module list is
// hidden by physicslib4-docs.css, so the header's switch is the only one, as on the rest of the site.
(function () {
  var root = document.documentElement;

  function current() {
    return root.classList.contains('dark-theme') ? 'dark' : 'light';
  }

  function applyTo(doc, theme) {
    var html = doc.documentElement;
    html.classList.toggle('dark-theme', theme === 'dark');
    html.classList.toggle('light-theme', theme !== 'dark');
    if (html.getAttribute('data-theme') !== theme) html.setAttribute('data-theme', theme);
  }

  function frames() {
    // The module-list frame of a page; inside the frame itself, its parent page.
    var docs = [];
    document.querySelectorAll('iframe.navframe').forEach(function (frame) {
      try { if (frame.contentDocument) docs.push(frame.contentDocument); } catch (e) { /* other origin */ }
    });
    try { if (window.parent !== window && window.parent.document) docs.push(window.parent.document); } catch (e) { /* other origin */ }
    return docs;
  }

  function sync() {
    var theme = current();
    try { localStorage.setItem('theme', theme); } catch (e) { /* storage unavailable */ }
    applyTo(document, theme);
    frames().forEach(function (doc) { applyTo(doc, theme); });
  }

  sync();
  new MutationObserver(sync).observe(root, { attributes: true, attributeFilter: ['class'] });
  // color-scheme.js may set `data-theme` from an older `theme` value; the site's class wins.
  new MutationObserver(function () {
    if (root.getAttribute('data-theme') !== current()) root.setAttribute('data-theme', current());
  }).observe(root, { attributes: true, attributeFilter: ['data-theme'] });
  window.addEventListener('DOMContentLoaded', function () {
    document.querySelectorAll('iframe.navframe').forEach(function (frame) {
      frame.addEventListener('load', sync);
    });
  });
})();
