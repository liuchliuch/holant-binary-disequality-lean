import Holant.Pauli.ExoticKlein.SixPortDirectionAction

/-! Sound transport of the full arbitrary-scale statement along actual
residual actions. Concrete physical generators are supplied separately. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

 theorem baseCard_normalizedTensor (state : DirectionTriple) (scale : Fin 4 → ℂ) (i : Fin 4) :
    baseCard (labelEquiv i) (normalizedTensor state scale) =
      fun z => scale i*optionDirection (cardDirections state i) z := by
  funext z
  have htail (u v : Bool) : tail4 (Fin.cons u (Fin.cons v z)) = z := rfl
  have hone (u v : Bool) : (Fin.cons u (Fin.cons v z) : Fin 6 → Bool) 1 = v := rfl
  have he : baseCard (labelEquiv i) (normalizedTensor state scale) z =
      ∑ j : Fin 4, scale j*Kernel.pair (dual (labelEquiv i)) (E (labelEquiv j))*
        optionDirection (cardDirections state j) z := by
    simp only [baseCard,normalizedTensor,Kernel.pair,Fintype.sum_bool,Fin.sum_univ_succ,
      Fin.sum_univ_zero,htail,hone,Fin.cons_zero,Fin.cons_succ]
    ring
  rw [he]
  simp only [dual_pair,Equiv.apply_eq_iff_eq,mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
  simp

 structure ResidualAction where
  direction : Equiv.Perm Direction
  coefficient : Direction → ℂ
  coefficient_ne_zero : ∀ d, coefficient d ≠ 0
  quad : Signature ℂ 4 → Signature ℂ 4
  full : Signature ℂ 6 → Signature ℂ 6
  quad_zero : quad 0 = 0
  quad_scale : ∀ h s, quad (fun x => s*h x) = fun x => s*quad h x
  quad_direction : ∀ d, quad (directionTensor d) = fun x => coefficient d*directionTensor (direction d) x
  cards : ∀ h a, baseCard a (full h) = quad (baseCard a h)
  safe : ∀ h, AllPhysicalSafe h → AllPhysicalSafe (full h)
  nonzero : ∀ h, h ≠ 0 → full h ≠ 0
  descend : ∀ h, IsProduct (full h) → IsProduct h

namespace ResidualAction

 def mapState (action : ResidualAction) (state : DirectionTriple) : DirectionTriple :=
  fun j => (state j).map action.direction

 def mapScale (action : ResidualAction) (state : DirectionTriple) (scale : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun i => match cardDirections state i with
    | none => 0
    | some d => scale i*action.coefficient d

 theorem cardDirections_mapState (action : ResidualAction) (hfix : action.direction baseDirection = baseDirection)
    (state : DirectionTriple) (i : Fin 4) :
    cardDirections (action.mapState state) i = (cardDirections state i).map action.direction := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [cardDirections,Fin.cons_zero,Option.map_some] using congrArg some hfix.symm
  · rfl

 theorem admissible_map (action : ResidualAction) (hfix : action.direction baseDirection = baseDirection)
    (state : DirectionTriple) (scale : Fin 4 → ℂ) (ha : Admissible state scale) :
    Admissible (action.mapState state) (action.mapScale state scale) := by
  intro i
  rw [action.cardDirections_mapState hfix]
  have hi := ha i
  cases hd : cardDirections state i with
  | none => simp only [hd,mapScale,Option.map_none,Option.isSome_none,Bool.false_eq_true,ite_false]
  | some d =>
    simp only [hd,mapScale,Option.map_some,Option.isSome_some,ite_true]
    have hs : scale i ≠ 0 := by simpa only [hd,Option.isSome_some,ite_true] using hi
    exact mul_ne_zero hs (action.coefficient_ne_zero d)

 theorem normalizedTensor_map (action : ResidualAction) (hfix : action.direction baseDirection = baseDirection)
    (state : DirectionTriple) (scale : Fin 4 → ℂ) :
    action.full (normalizedTensor state scale) =
      normalizedTensor (action.mapState state) (action.mapScale state scale) := by
  apply normalizedTensor_of_cards
  intro i
  rw [action.cards,baseCard_normalizedTensor,action.cardDirections_mapState hfix]
  cases hd : cardDirections state i with
  | none =>
    have hz : (fun z => scale i*optionDirection (none : Option Direction) z) = (0 : Signature ℂ 4) := by
      funext z
      simp [optionDirection,optionDirectionOver]
    rw [hz,action.quad_zero]
    funext z
    simp [mapScale,hd]
  | some d =>
    change action.quad (fun z => scale i*directionTensor d z) = _
    rw [action.quad_scale,action.quad_direction]
    funext z
    simp only [mapScale,hd,Option.map_some,optionDirection,optionDirectionOver,directionTensor]
    ring

 def compose (first second : ResidualAction) : ResidualAction where
  direction := first.direction.trans second.direction
  coefficient d := first.coefficient d*second.coefficient (first.direction d)
  coefficient_ne_zero d := mul_ne_zero (first.coefficient_ne_zero d) (second.coefficient_ne_zero _)
  quad h := second.quad (first.quad h)
  full h := second.full (first.full h)
  quad_zero := by rw [first.quad_zero,second.quad_zero]
  quad_scale h s := by rw [first.quad_scale,second.quad_scale]
  quad_direction d := by
    rw [first.quad_direction,second.quad_scale,second.quad_direction]
    funext x
    simp only [Equiv.trans_apply]
    ring
  cards h a := by rw [second.cards,first.cards]
  safe h hs := second.safe _ (first.safe h hs)
  nonzero h hn := second.nonzero _ (first.nonzero h hn)
  descend h hp := first.descend h (second.descend _ hp)

end ResidualAction

/-- The complete normalized semantic statement for one direction triple. -/
 def Solved (state : DirectionTriple) : Prop := ∀ scale : Fin 4 → ℂ,
  Admissible state scale → AllPhysicalSafe (normalizedTensor state scale) →
  normalizedTensor state scale ≠ 0 → IsProduct (normalizedTensor state scale)

 theorem solved_of_certificate (state : DirectionTriple) (certificate : LinearCertificate.Certificate 4 64 60 48 960)
    (hc : certificate.check (problem state) (initialRows state) = true) : Solved state := by
  intro scale ha hs hn
  exact normalized_product_of_checked_physical state certificate hc scale ha hs hn

 theorem ResidualAction.solved_back (action : ResidualAction) (hfix : action.direction baseDirection = baseDirection)
    (state : DirectionTriple) (hs : Solved (action.mapState state)) : Solved state := by
  intro scale ha hsafe hn
  apply action.descend
  have ha' := action.admissible_map hfix state scale ha
  have he := action.normalizedTensor_map hfix state scale
  have hs' := action.safe _ hsafe
  have hn' := action.nonzero _ hn
  rw [he] at hs' hn' ⊢
  exact hs _ ha' hs' hn'

 theorem six_port_product_of_solved (allSolved : ∀ state : DirectionTriple, Solved state)
    (h : Signature ℂ 6) (hn : h ≠ 0) (hs : AllPhysicalSafe h) : IsProduct h := by
  obtain ⟨g,hsg,hng,hbg,descend⟩ := exists_normalization h hn hs
  obtain ⟨state,scale,ha,he⟩ := exists_prepared_form g hsg hbg
  apply descend
  rw [he] at hsg hng ⊢
  exact allSolved state scale ha hsg hng

end
end Holant.Pauli.ExoticKlein.SixPort
