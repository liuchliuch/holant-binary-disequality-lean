import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_300 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,0,0),x,y,z) (printedFamilyWitness ((3,0,0),x,y,z)) := by decide

theorem dense_witness_301 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,0,1),x,y,z) (printedFamilyWitness ((3,0,1),x,y,z)) := by decide

theorem dense_witness_302 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,0,2),x,y,z) (printedFamilyWitness ((3,0,2),x,y,z)) := by decide

theorem dense_witness_303 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,0,3),x,y,z) (printedFamilyWitness ((3,0,3),x,y,z)) := by decide

theorem dense_witness_310 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,1,0),x,y,z) (printedFamilyWitness ((3,1,0),x,y,z)) := by decide

theorem dense_witness_311 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,1,1),x,y,z) (printedFamilyWitness ((3,1,1),x,y,z)) := by decide

theorem dense_witness_312 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,1,2),x,y,z) (printedFamilyWitness ((3,1,2),x,y,z)) := by decide

theorem dense_witness_313 : ∀ x y z : Bool,
    ValidFamilyWitness ((3,1,3),x,y,z) (printedFamilyWitness ((3,1,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
