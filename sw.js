/* Service worker för Fantasy Rinken (installerbar app / PWA).
   Sidan och ikonerna sparas så att appen startar snabbt och även utan nät.
   Data (Statnet-filen och Fantasy SHL) hämtas alltid färskt och cachas aldrig här. */
var VERSION = 'fr-2.2.1';
var SHELL = ['./', 'index.html', 'manifest.webmanifest', 'icon-192.png', 'icon-512.png', 'icon-180.png'];

self.addEventListener('install', function (e) {
  e.waitUntil(caches.open(VERSION).then(function (c) { return c.addAll(SHELL); }).then(function () { return self.skipWaiting(); }));
});
self.addEventListener('activate', function (e) {
  e.waitUntil(caches.keys().then(function (keys) {
    return Promise.all(keys.filter(function (k) { return k !== VERSION; }).map(function (k) { return caches.delete(k); }));
  }).then(function () { return self.clients.claim(); }));
});
self.addEventListener('fetch', function (e) {
  var url = new URL(e.request.url);
  if (e.request.method !== 'GET' || url.origin !== self.location.origin) return; // Fantasy SHL m.m.: rör inte
  if (url.pathname.indexOf('/data/') >= 0) return;                               // Statnet-data: alltid färsk
  // Sidan: nätet först (nya versioner syns direkt), sparad kopia om nätet saknas.
  e.respondWith(fetch(e.request).then(function (res) {
    if (res && res.ok) { var copy = res.clone(); caches.open(VERSION).then(function (c) { c.put(e.request, copy); }); }
    return res;
  }).catch(function () { return caches.match(e.request).then(function (m) { return m || caches.match('index.html'); }); }));
});
