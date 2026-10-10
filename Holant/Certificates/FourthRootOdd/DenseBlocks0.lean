import Holant.Certificates.FourthRootOdd.DensePrinted
namespace Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

theorem dense_witness_000 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,0,0),x,y,z) (printedFamilyWitness ((0,0,0),x,y,z)) := by decide

theorem dense_witness_001 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,0,1),x,y,z) (printedFamilyWitness ((0,0,1),x,y,z)) := by decide

theorem dense_witness_002 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,0,2),x,y,z) (printedFamilyWitness ((0,0,2),x,y,z)) := by decide

theorem dense_witness_003 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,0,3),x,y,z) (printedFamilyWitness ((0,0,3),x,y,z)) := by decide

theorem dense_witness_010 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,1,0),x,y,z) (printedFamilyWitness ((0,1,0),x,y,z)) := by decide

theorem dense_witness_011 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,1,1),x,y,z) (printedFamilyWitness ((0,1,1),x,y,z)) := by decide

theorem dense_witness_012 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,1,2),x,y,z) (printedFamilyWitness ((0,1,2),x,y,z)) := by decide

theorem dense_witness_013 : ∀ x y z : Bool,
    ValidFamilyWitness ((0,1,3),x,y,z) (printedFamilyWitness ((0,1,3),x,y,z)) := by decide

end Holant.Certificates.FourthRootOdd
