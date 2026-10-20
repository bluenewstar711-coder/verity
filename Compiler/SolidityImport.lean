import Compiler.SolidityImport.Profile
import Compiler.SolidityImport.Report
import Compiler.SolidityImport.AstIndex
import Compiler.SolidityImport.TypeClassifier

/-!
# Modular `SolidityImport` Core Facade (`Compiler.SolidityImport`)

Lightweight root facade exposing the modular `SolidityImport` components:
* `Compiler.SolidityImport.Profile`: pinned `solc` release and optimizer settings.
* `Compiler.SolidityImport.Report`: slice translation report and provenance records.
* `Compiler.SolidityImport.AstIndex`: $\mathcal{O}(1)$ precomputed `Std.HashMap` AST index.
* `Compiler.SolidityImport.TypeClassifier`: total classification algebra for
  Solidity `typeString` and `typeIdentifier` descriptors.
-/
