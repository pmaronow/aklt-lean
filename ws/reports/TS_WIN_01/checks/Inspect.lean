import AKLT.Blueprint.Win.NodesShell

open AKLT.Defs AKLT.Blueprint.Win

-- Inspection only: no proofs or declarations of mathematical claims.
#print ShellScaleStatement
#print CloseCornerStatement
#print ExceptionalLocalizationStatement
#print RadiusGapStatement
#print ExceptionalCountStatement
#print SideCornerWitnessStatement
#print NearShellCountStatement
#print ShellInclusionStatement
#print ShellSetup
#print ParallelClearance
#print setDistance
#print squareCorners
#print shellRadius
#print farVolume
#print nearShell
#print exceptionalIndices

#eval (squareCorners (0, 0) 0).card
#eval ((squareCorners (0, 0) 0).filter fun c => supDist c (0, -1) < 0).card
#eval ((squareCorners (0, 0) 1).filter fun c => supDist c (-1, -2) < 1).card
