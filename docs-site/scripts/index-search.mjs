import { spawnSync } from "node:child_process";
import { cpSync, existsSync, readdirSync, rmSync } from "node:fs";
import { fileURLToPath } from "node:url";

const source = ".next/server/app";
const staged = "public/_pagefind-source";

function hasHtml(directory) {
  const entries = readdirSync(directory, { recursive: true, withFileTypes: true });
  return entries.some((entry) => entry.isFile() && entry.name.endsWith(".html"));
}

if (!existsSync(source) || !hasHtml(source)) {
  if (process.env.VERCEL) {
    console.log("Built HTML is not available on Vercel; leaving search index unchanged.");
    process.exit(0);
  }
  throw new Error(`No HTML files found in ${source}`);
}

rmSync(staged, { recursive: true, force: true });
cpSync(source, staged, { recursive: true });

const result = spawnSync(
  fileURLToPath(new URL("../node_modules/.bin/pagefind", import.meta.url)),
  ["--site", staged, "--output-path", "public/_pagefind"],
  { stdio: "inherit" },
);

rmSync(staged, { recursive: true, force: true });
process.exit(result.status ?? 1);
