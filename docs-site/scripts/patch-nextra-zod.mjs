import { readFileSync, writeFileSync } from "node:fs";

const layoutPath = new URL(
  "../node_modules/nextra-theme-docs/dist/layout.js",
  import.meta.url,
);

const source = readFileSync(layoutPath, "utf8");
const needle = `    ({
      children,
      ...themeConfig
    } = t0);`;
const patched = `    ({
      children,
      ...themeConfig
    } = t0);
    // zod 4.6.6 treats a missing key as invalid. Nextra removes children
    // before validating, so put the same value back for that check only.
    themeConfig.children = children;`;

if (source.includes("themeConfig.children = children;")) {
  process.exit(0);
}

if (!source.includes(needle)) {
  throw new Error(`nextra-theme-docs layout patch point not found in ${layoutPath.pathname}`);
}

writeFileSync(layoutPath, source.replace(needle, patched));
