import GrayNecklaces

/-! Axiom audit for the main theorem. Run with `lake env lean --trust=0 GrayNecklaces/Audit.lean`. -/

#check @GrayNecklaces.oddPrimeDegniDrisko
#print axioms GrayNecklaces.oddPrimeDegniDrisko
