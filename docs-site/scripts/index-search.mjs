import { spawnSync } from "node:child_process";
import { cpSync, rmSync } from "node:fs";
import { fileURLToPath } from "node:url";

const source = ".next/server/app";
const staged = "public/_pagefind-source";

rmSync(staged, { recursive: true, force: true });
cpSync(source, staged, { recursive: true });

const result = spawnSync(
  fileURLToPath(new URL("../node_modules/.bin/pagefind", import.meta.url)),
  ["--site", staged, "--output-path", "public/_pagefind"],
  { stdio: "inherit" },
);

rmSync(staged, { recursive: true, force: true });
process.exit(result.status ?? 1);
