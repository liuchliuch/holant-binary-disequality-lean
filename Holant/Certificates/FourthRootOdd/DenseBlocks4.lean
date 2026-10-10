import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_200 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,0,0),x,y,z) (printedFamilyWitness ((2,0,0),x,y,z)) := by decide

theorem dense_witness_201 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,0,1),x,y,z) (printedFamilyWitness ((2,0,1),x,y,z)) := by decide

theorem dense_witness_202 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,0,2),x,y,z) (printedFamilyWitness ((2,0,2),x,y,z)) := by decide

theorem dense_witness_203 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,0,3),x,y,z) (printedFamilyWitness ((2,0,3),x,y,z)) := by decide

theorem dense_witness_210 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,1,0),x,y,z) (printedFamilyWitness ((2,1,0),x,y,z)) := by decide

theorem dense_witness_211 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,1,1),x,y,z) (printedFamilyWitness ((2,1,1),x,y,z)) := by decide

theorem dense_witness_212 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,1,2),x,y,z) (printedFamilyWitness ((2,1,2),x,y,z)) := by decide

theorem dense_witness_213 : ∀ x y z : Bool,
    ValidFamilyWitness ((2,1,3),x,y,z) (printedFamilyWitness ((2,1,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
