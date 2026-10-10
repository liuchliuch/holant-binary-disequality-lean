import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_020 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,2,0),x,y,z) (printedFamilyWitness ((0,2,0),x,y,z)) := by decide

theorem dense_witness_021 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,2,1),x,y,z) (printedFamilyWitness ((0,2,1),x,y,z)) := by decide

theorem dense_witness_022 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,2,2),x,y,z) (printedFamilyWitness ((0,2,2),x,y,z)) := by decide

theorem dense_witness_023 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,2,3),x,y,z) (printedFamilyWitness ((0,2,3),x,y,z)) := by decide

theorem dense_witness_030 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,3,0),x,y,z) (printedFamilyWitness ((0,3,0),x,y,z)) := by decide

theorem dense_witness_031 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,3,1),x,y,z) (printedFamilyWitness ((0,3,1),x,y,z)) := by decide

theorem dense_witness_032 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,3,2),x,y,z) (printedFamilyWitness ((0,3,2),x,y,z)) := by decide

theorem dense_witness_033 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,3,3),x,y,z) (printedFamilyWitness ((0,3,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
