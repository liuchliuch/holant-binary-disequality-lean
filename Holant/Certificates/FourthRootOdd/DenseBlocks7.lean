import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_320 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,2,0),x,y,z) (printedFamilyWitness ((3,2,0),x,y,z)) := by decide

theorem dense_witness_321 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,2,1),x,y,z) (printedFamilyWitness ((3,2,1),x,y,z)) := by decide

theorem dense_witness_322 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,2,2),x,y,z) (printedFamilyWitness ((3,2,2),x,y,z)) := by decide

theorem dense_witness_323 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,2,3),x,y,z) (printedFamilyWitness ((3,2,3),x,y,z)) := by decide

theorem dense_witness_330 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,3,0),x,y,z) (printedFamilyWitness ((3,3,0),x,y,z)) := by decide

theorem dense_witness_331 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,3,1),x,y,z) (printedFamilyWitness ((3,3,1),x,y,z)) := by decide

theorem dense_witness_332 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,3,2),x,y,z) (printedFamilyWitness ((3,3,2),x,y,z)) := by decide

theorem dense_witness_333 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,3,3),x,y,z) (printedFamilyWitness ((3,3,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
