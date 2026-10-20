import Compiler.MainDriver
import Compiler.CompilationModel.TrustSurfaceLinear

unsafe def main (args : List String) : IO Unit :=
  Compiler.Main.run args
