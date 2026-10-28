// Light and dark theme of the blueprint, shared with the physicslib4 website and books.
//
// The theme is the class `light-theme` or `dark-theme` on <html>, as on the website. The
// choice is kept in localStorage under the keys of the website's theme script (`theme-local`,
// the reader's choice; `theme-system`, the system preference it was made under), so a reader
// who switches theme on one of the documents sees the same theme on the others. Loaded in the
// <head>, before the page is drawn.
(function () {
  function get(key) {
    try { return localStorage.getItem(key); } catch (e) { return null; }
  }
  function set(key, value) {
    try { localStorage.setItem(key, value); } catch (e) { /* storage unavailable */ }
  }
  function apply(theme) {
    var root = document.documentElement;
    root.classList.toggle('dark-theme', theme === 'dark');
    root.classList.toggle('light-theme', theme !== 'dark');
  }

  var media = window.matchMedia('(prefers-color-scheme: dark)');
  var system = media.matches ? 'dark' : 'light';
  var storedSystem = get('theme-system');
  var local = get('theme-local');
  if (storedSystem !== system && (!local || local === storedSystem)) {
    // The system preference changed and the reader had not overridden the old one: follow it.
    set('theme-local', system);
    apply(system);
  } else {
    apply(local || system);
  }

  media.addEventListener('change', function (e) {
    var newSystem = e.matches ? 'dark' : 'light';
    var oldSystem = get('theme-system');
    var current = get('theme-local');
    if (newSystem !== oldSystem) {
      set('theme-system', newSystem);
      if (!current || current === oldSystem) {
        set('theme-local', newSystem);
        apply(newSystem);
      }
    }
  });

  window.addEventListener('DOMContentLoaded', function () {
    document.querySelectorAll('.change-theme').forEach(function (button) {
      button.addEventListener('click', function () {
        var theme = document.documentElement.classList.contains('dark-theme') ? 'light' : 'dark';
        set('theme-local', theme);
        apply(theme);
      });
    });
  });
})();
