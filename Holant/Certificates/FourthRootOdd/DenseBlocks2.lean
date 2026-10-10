import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_100 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,0,0),x,y,z) (printedFamilyWitness ((1,0,0),x,y,z)) := by decide

theorem dense_witness_101 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,0,1),x,y,z) (printedFamilyWitness ((1,0,1),x,y,z)) := by decide

theorem dense_witness_102 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,0,2),x,y,z) (printedFamilyWitness ((1,0,2),x,y,z)) := by decide

theorem dense_witness_103 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,0,3),x,y,z) (printedFamilyWitness ((1,0,3),x,y,z)) := by decide

theorem dense_witness_110 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,1,0),x,y,z) (printedFamilyWitness ((1,1,0),x,y,z)) := by decide

theorem dense_witness_111 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,1,1),x,y,z) (printedFamilyWitness ((1,1,1),x,y,z)) := by decide

theorem dense_witness_112 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,1,2),x,y,z) (printedFamilyWitness ((1,1,2),x,y,z)) := by decide

theorem dense_witness_113 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,1,3),x,y,z) (printedFamilyWitness ((1,1,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
