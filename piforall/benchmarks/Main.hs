import Criterion.Main
import PiForall.Rebound.Modules qualified as AutoPiForall
import PiForall.Unbound.Modules qualified as UnPiForall

-- TODO: suppress IO

prefixes = ["pi/std"]

b name path =
  bgroup
    name
    [ bench "Unbound" $ nfIO (UnPiForall.goFilename prefixes path),
      bench "Rebound" $ nfIO (AutoPiForall.goFilename prefixes path)
    ]

main =
  defaultMain
    [ bgroup
        "Compute"
        [ b "Lennart" "pi/examples/cLennart.pi",
          b "Compiler" "pi/examples/cCompiler.pi"
        ],
      bgroup
        "Typechecking"
        [ b "Compiler" "pi/examples/Compiler.pi",
          b "AVL (System F)" "pi/examples/AVL_F.pi",
          b "AVL (Dependently-typed)" "pi/examples/AVL.pi"
        ]
    ]