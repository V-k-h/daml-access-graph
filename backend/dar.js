// backend/dar.js
//
// Light DAR (Daml archive) inspection helpers. A DAR is just a ZIP whose
// META-INF/MANIFEST.MF names the main DALF. We use the system `unzip` (no npm
// dependency) to read the manifest for provenance metadata. The actual
// Daml-LF extraction goes through the SDK (`damlc inspect`), which reads the
// DAR directly, so unzip here is only for nice-to-have metadata.

import { execFileSync } from 'node:child_process';

/**
 * @param {string} darPath
 * @returns {{name: string|null, mainDalf: string|null, dalfs: string[]}}
 */
export function readDarManifest(darPath) {
  let manifest = '';
  try {
    manifest = execFileSync('unzip', ['-p', darPath, 'META-INF/MANIFEST.MF'], {
      encoding: 'utf8',
    });
  } catch (_) {
    return { name: null, mainDalf: null, dalfs: [] };
  }
  // MANIFEST.MF folds long lines with a leading space on continuation lines.
  const unfolded = manifest.replace(/\r?\n /g, '');
  const get = (key) => {
    const m = unfolded.match(new RegExp(`^${key}:\\s*(.+)$`, 'm'));
    return m ? m[1].trim() : null;
  };
  const mainDalf = get('Main-Dalf');
  const name = get('Name');
  const dalfsRaw = get('Dalfs') || '';
  const dalfs = dalfsRaw
    .split(',')
    .map((s) => s.trim())
    .filter(Boolean);
  return { name, mainDalf, dalfs };
}
