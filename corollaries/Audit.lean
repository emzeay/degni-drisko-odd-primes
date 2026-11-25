import NecklaceGrayCode
import SingleTrack

/-! Axiom audit for the corollaries. Run with `lake env lean --trust=0 corollaries/Audit.lean`
after `lake build Corollaries`. -/

-- Problem P17 at odd prime lengths: a Gray code for necklaces.
#check @GrayNecklaces.NecklaceGrayCode.necklaceGrayCode_of_main
#print axioms GrayNecklaces.NecklaceGrayCode.necklaceGrayCode_of_main
#check @GrayNecklaces.NecklaceGrayCode.necklaceGrayCode
#print axioms GrayNecklaces.NecklaceGrayCode.necklaceGrayCode

-- Problem P13: the Degni–Drisko property in the form of Dzoba's Theorem A hypothesis.
#check @GrayNecklaces.SingleTrack.ddProperty_of_main
#print axioms GrayNecklaces.SingleTrack.ddProperty_of_main
#check @GrayNecklaces.SingleTrack.ddProperty
#print axioms GrayNecklaces.SingleTrack.ddProperty
