import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_220 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,2,0),x,y,z) (printedFamilyWitness ((2,2,0),x,y,z)) := by decide

theorem dense_witness_221 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,2,1),x,y,z) (printedFamilyWitness ((2,2,1),x,y,z)) := by decide

theorem dense_witness_222 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,2,2),x,y,z) (printedFamilyWitness ((2,2,2),x,y,z)) := by decide

theorem dense_witness_223 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,2,3),x,y,z) (printedFamilyWitness ((2,2,3),x,y,z)) := by decide

theorem dense_witness_230 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,3,0),x,y,z) (printedFamilyWitness ((2,3,0),x,y,z)) := by decide

theorem dense_witness_231 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,3,1),x,y,z) (printedFamilyWitness ((2,3,1),x,y,z)) := by decide

theorem dense_witness_232 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,3,2),x,y,z) (printedFamilyWitness ((2,3,2),x,y,z)) := by decide

theorem dense_witness_233 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,3,3),x,y,z) (printedFamilyWitness ((2,3,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
