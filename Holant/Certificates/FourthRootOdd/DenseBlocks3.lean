import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_120 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,2,0),x,y,z) (printedFamilyWitness ((1,2,0),x,y,z)) := by decide

theorem dense_witness_121 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,2,1),x,y,z) (printedFamilyWitness ((1,2,1),x,y,z)) := by decide

theorem dense_witness_122 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,2,2),x,y,z) (printedFamilyWitness ((1,2,2),x,y,z)) := by decide

theorem dense_witness_123 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,2,3),x,y,z) (printedFamilyWitness ((1,2,3),x,y,z)) := by decide

theorem dense_witness_130 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,3,0),x,y,z) (printedFamilyWitness ((1,3,0),x,y,z)) := by decide

theorem dense_witness_131 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,3,1),x,y,z) (printedFamilyWitness ((1,3,1),x,y,z)) := by decide

theorem dense_witness_132 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,3,2),x,y,z) (printedFamilyWitness ((1,3,2),x,y,z)) := by decide

theorem dense_witness_133 : ∀ x y z : Bool,
    ValidFamilyWitness ((1,3,3),x,y,z) (printedFamilyWitness ((1,3,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
