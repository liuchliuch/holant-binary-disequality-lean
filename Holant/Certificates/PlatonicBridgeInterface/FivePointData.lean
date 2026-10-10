import Holant.Certificates.RainbowOrbit.GroupIcosahedralData
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! The action on the five left cosets of the twelve displayed tetrahedral
classes. All entries are checked against the existing actual multiplication
table; no abstract identification of a group of order sixty is assumed. -/
namespace Holant.Certificates.PlatonicBridgeInterface
open Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def tetrahedralCoset : Fin 5 → Fin 12 → Fin 60 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11],![12,17,23,26,30,34,39,40,45,49,52,59],![13,19,20,27,29,32,37,43,44,50,54,58],![14,18,22,24,31,33,36,41,47,48,55,57],![15,16,21,25,28,35,38,42,46,51,53,56]]

def cosetLabel : Fin 60 → Fin 5 :=
  ![0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,4,1,3,2,2,4,3,1,3,4,1,2,4,2,1,3,2,3,1,4,3,2,4,1,1,3,4,2,2,1,4,3,3,1,2,4,1,4,2,3,4,3,2,1]

def fiveAction : Fin 60 → Fin 5 → Fin 5 :=
  ![![0,1,2,3,4],![0,4,3,2,1],![0,3,4,1,2],![0,2,1,4,3],![0,2,4,3,1],![0,2,3,1,4],![0,1,4,2,3],![0,4,2,1,3],![0,3,2,4,1],![0,1,3,4,2],![0,3,1,2,4],![0,4,1,3,2],![1,0,3,2,4],![2,4,0,3,1],![3,4,2,0,1],![4,1,3,2,0],![4,3,2,1,0],![1,0,4,3,2],![3,1,4,0,2],![2,3,0,1,4],![2,1,0,4,3],![4,2,1,3,0],![3,2,1,0,4],![1,0,2,4,3],![3,1,0,2,4],![4,0,2,3,1],![1,4,2,3,0],![2,1,3,0,4],![4,0,3,1,2],![2,3,4,0,1],![1,3,4,2,0],![3,4,0,1,2],![2,4,1,0,3],![3,2,0,4,1],![1,2,3,4,0],![4,0,1,2,3],![3,0,2,1,4],![2,1,4,3,0],![4,1,0,3,2],![1,3,2,0,4],![1,4,3,0,2],![3,0,4,2,1],![4,3,0,2,1],![2,4,3,1,0],![2,3,1,4,0],![1,2,4,0,3],![4,2,0,1,3],![3,0,1,4,2],![3,1,2,4,0],![1,2,0,3,4],![2,0,1,3,4],![4,1,2,0,3],![1,4,0,2,3],![4,2,3,0,1],![2,0,3,4,1],![3,4,1,2,0],![4,3,1,0,2],![3,2,4,1,0],![2,0,4,1,3],![1,3,0,4,2]]

def fiveInverse : Fin 60 → Fin 5 → Fin 5 :=
  ![![0,1,2,3,4],![0,4,3,2,1],![0,3,4,1,2],![0,2,1,4,3],![0,4,1,3,2],![0,3,1,2,4],![0,1,3,4,2],![0,3,2,4,1],![0,4,2,1,3],![0,1,4,2,3],![0,2,3,1,4],![0,2,4,3,1],![1,0,3,2,4],![2,4,0,3,1],![3,4,2,0,1],![4,1,3,2,0],![4,3,2,1,0],![1,0,4,3,2],![3,1,4,0,2],![2,3,0,1,4],![2,1,0,4,3],![4,2,1,3,0],![3,2,1,0,4],![1,0,2,4,3],![2,1,3,0,4],![1,4,2,3,0],![4,0,2,3,1],![3,1,0,2,4],![1,3,4,2,0],![3,4,0,1,2],![4,0,3,1,2],![2,3,4,0,1],![3,2,0,4,1],![2,4,1,0,3],![4,0,1,2,3],![1,2,3,4,0],![1,3,2,0,4],![4,1,0,3,2],![2,1,4,3,0],![3,0,2,1,4],![3,0,4,2,1],![1,4,3,0,2],![2,4,3,1,0],![4,3,0,2,1],![4,2,0,1,3],![3,0,1,4,2],![2,3,1,4,0],![1,2,4,0,3],![4,1,2,0,3],![2,0,1,3,4],![1,2,0,3,4],![3,1,2,4,0],![2,0,3,4,1],![3,4,1,2,0],![1,4,0,2,3],![4,2,3,0,1],![3,2,4,1,0],![4,3,1,0,2],![1,3,0,4,2],![2,0,4,1,3]]

def inverseIndex : Fin 60 → Fin 60 :=
  ![0,1,2,3,11,10,9,8,7,6,5,4,12,13,14,15,16,17,18,19,20,21,22,23,27,26,25,24,30,31,28,29,33,32,35,34,39,38,37,36,41,40,43,42,46,47,44,45,51,50,49,48,54,55,52,53,57,56,59,58]

theorem five_inverse_left : ∀ g x, fiveInverse g (fiveAction g x) = x := by decide +kernel
theorem five_inverse_right : ∀ g x, fiveAction g (fiveInverse g x) = x := by decide +kernel

def fivePermutation (g : Fin 60) : Equiv.Perm (Fin 5) where
  toFun := fiveAction g
  invFun := fiveInverse g
  left_inv := five_inverse_left g
  right_inv := five_inverse_right g

theorem five_action_faithful : ∀ g h, (∀ x, fiveAction g x = fiveAction h x) → g = h := by decide +kernel

theorem five_action_even : ∀ g, (fivePermutation g).sign = 1 := by decide +kernel

theorem five_action_identity : ∀ x, fiveAction 0 x = x := by decide +kernel

theorem inverse_product : ∀ g, icosahedralProductIndex (inverseIndex g) g = 0 := by decide +kernel

end Holant.Certificates.PlatonicBridgeInterface
