import Holant.Certificates.PlatonicBridgeInterface.FivePointRows0
import Holant.Certificates.PlatonicBridgeInterface.FivePointRows1
import Holant.Certificates.PlatonicBridgeInterface.FivePointRows2
import Holant.Certificates.PlatonicBridgeInterface.FivePointRows3
import Holant.Certificates.PlatonicBridgeInterface.FivePointRows4
import Holant.Certificates.PlatonicBridgeInterface.FivePointRows5
import Mathlib.Data.Fintype.EquivFin

namespace Holant.Certificates.PlatonicBridgeInterface
open Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem five_action_product (g h : Fin 60) (x : Fin 5) :
    fiveAction (icosahedralProductIndex g h) x = fiveAction g (fiveAction h x) := by
  fin_cases g
  · exact five_product_row_0 h x
  · exact five_product_row_1 h x
  · exact five_product_row_2 h x
  · exact five_product_row_3 h x
  · exact five_product_row_4 h x
  · exact five_product_row_5 h x
  · exact five_product_row_6 h x
  · exact five_product_row_7 h x
  · exact five_product_row_8 h x
  · exact five_product_row_9 h x
  · exact five_product_row_10 h x
  · exact five_product_row_11 h x
  · exact five_product_row_12 h x
  · exact five_product_row_13 h x
  · exact five_product_row_14 h x
  · exact five_product_row_15 h x
  · exact five_product_row_16 h x
  · exact five_product_row_17 h x
  · exact five_product_row_18 h x
  · exact five_product_row_19 h x
  · exact five_product_row_20 h x
  · exact five_product_row_21 h x
  · exact five_product_row_22 h x
  · exact five_product_row_23 h x
  · exact five_product_row_24 h x
  · exact five_product_row_25 h x
  · exact five_product_row_26 h x
  · exact five_product_row_27 h x
  · exact five_product_row_28 h x
  · exact five_product_row_29 h x
  · exact five_product_row_30 h x
  · exact five_product_row_31 h x
  · exact five_product_row_32 h x
  · exact five_product_row_33 h x
  · exact five_product_row_34 h x
  · exact five_product_row_35 h x
  · exact five_product_row_36 h x
  · exact five_product_row_37 h x
  · exact five_product_row_38 h x
  · exact five_product_row_39 h x
  · exact five_product_row_40 h x
  · exact five_product_row_41 h x
  · exact five_product_row_42 h x
  · exact five_product_row_43 h x
  · exact five_product_row_44 h x
  · exact five_product_row_45 h x
  · exact five_product_row_46 h x
  · exact five_product_row_47 h x
  · exact five_product_row_48 h x
  · exact five_product_row_49 h x
  · exact five_product_row_50 h x
  · exact five_product_row_51 h x
  · exact five_product_row_52 h x
  · exact five_product_row_53 h x
  · exact five_product_row_54 h x
  · exact five_product_row_55 h x
  · exact five_product_row_56 h x
  · exact five_product_row_57 h x
  · exact five_product_row_58 h x
  · exact five_product_row_59 h x

theorem fivePermutation_injective : Function.Injective fivePermutation := by
  intro g h he
  exact five_action_faithful g h (fun x => congrArg (fun p : Equiv.Perm (Fin 5) => p x) he)

theorem fivePermutation_product (g h : Fin 60) :
    fivePermutation (icosahedralProductIndex g h) = fivePermutation g * fivePermutation h := by
  apply Equiv.ext
  intro x
  exact five_action_product g h x

def alternatingAction (g : Fin 60) : alternatingGroup (Fin 5) :=
  ⟨fivePermutation g, Equiv.Perm.mem_alternatingGroup.mpr (five_action_even g)⟩

theorem alternatingAction_injective : Function.Injective alternatingAction := by
  intro g h he
  exact fivePermutation_injective (congrArg Subtype.val he)

theorem alternatingAction_bijective : Function.Bijective alternatingAction := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨alternatingAction_injective, ?_⟩
  rw [Fintype.card_fin, card_alternatingGroup, Fintype.card_fin]
  decide

/-- A proved bijection onto all even permutations, after checking the actual
multiplication table on all3600 ordered pairs. Cardinality is used only for
surjectivity of this explicit faithful action. -/
noncomputable def indexAlternatingEquiv : Fin 60 ≃ alternatingGroup (Fin 5) :=
  Equiv.ofBijective alternatingAction alternatingAction_bijective

theorem indexAlternatingEquiv_product (g h : Fin 60) :
    indexAlternatingEquiv (icosahedralProductIndex g h) =
      indexAlternatingEquiv g * indexAlternatingEquiv h := by
  apply Subtype.ext
  exact fivePermutation_product g h

end Holant.Certificates.PlatonicBridgeInterface
