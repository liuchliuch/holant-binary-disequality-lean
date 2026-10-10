import Holant.ReedMuller.CharacterRecognition.LogicalCards
import Holant.ReedMuller.CharacterRecognition.SupportCoordinates
import Holant.ReedMuller.CharacterRecognition.SupportLocus

/-! Intrinsic source recognition in the original affine support. Logical
coordinates preserve the all-one word, so every direction actually tested
below is accessible in the original physical vector space. -/
namespace Holant.ReedMuller.CharacterRecognition
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {r : ℕ} {f : Signature AlgebraicComplex (2*r)}

theorem logical_direction_cards (hr : 4≤r) (A : ActualNormalForm f)
    (hd : CFlatSignedRadonCards (fun x => (f (wordVector x):ℂ)))
    (e : BinaryVector r ≃ₗ[ZMod 2] A.direction) (w : Word r)
    (hw : Accessible (supportEmbedding A.direction e (vectorWord w))) (l : ZMod 2) :
    ZeroOrFullCharacter (fun x =>
      (logicalCoefficient f A.shift A.direction e x:ℂ)+
        sign l*(logicalCoefficient f A.shift A.direction e (xor x w):ℂ)) := by
  let E := supportEmbedding A.direction e
  let v := E (vectorWord w)
  let g : BinaryVector (2*r) → ℂ := fun x => (f (wordVector x):ℂ)
  have hvU : v∈A.direction := (e (vectorWord w)).property
  have he (x : Word r) : A.shift+E (vectorWord (xor x w))=
      A.shift+E (vectorWord x)+v := by
    rw [vectorWord_xor,map_add]
    exact (add_assoc _ _ _).symm
  rcases A.signed_orbit_zero_or_full_character hr hd v hw hvU l with hz|hs
  · left
    intro x
    change g (A.shift+E (vectorWord x))+sign l*g (A.shift+E (vectorWord (xor x w)))=0
    rw [he]
    exact hz _
  · obtain ⟨F,hF,hcards⟩ := hd v hw
    have H := full_character_of_actual_signed_card g A.shift A.direction
      (A.direction_selfDual_character hr hd.plus) e F (by rwa [hF]) l (hcards _ l)
      (by simpa only [hF,g] using hs)
    rcases H with ⟨c,hc,ell,hell⟩
    right
    refine ⟨c,hc,ell,?_⟩
    intro x
    have hh := hell x
    rw [hF] at hh
    change g (A.shift+E (vectorWord x))+sign l*g (A.shift+E (vectorWord (xor x w)))=_
    rw [he]
    exact hh

/-- Pull-back coefficients keep the exact original nonzero scalar and the
constant phase. -/
theorem logical_phase_cards (hr : 4≤r) (A : ActualNormalForm f)
    (hd : CFlatSignedRadonCards (fun x => (f (wordVector x):ℂ)))
    (e : BinaryVector r ≃ₗ[ZMod 2] A.direction)
    (c : ℂ) (hc : c≠0) (Q : QuadraticPhase r)
    (he : ∀ x,(logicalCoefficient f A.shift A.direction e x:ℂ)=c*phase Q x)
    (w : Word r) (hw : Accessible (supportEmbedding A.direction e (vectorWord w)))
    (l : ZMod 2) : ZeroOrFullCharacter (directionCard Q w l) := by
  have H := logical_direction_cards hr A hd e w hw l
  have hh : (fun x => (logicalCoefficient f A.shift A.direction e x:ℂ)+
      sign l*(logicalCoefficient f A.shift A.direction e (xor x w):ℂ))=
      fun x => c*directionCard Q w l x := by
    funext x
    rw [he,he]
    unfold directionCard
    ring
  rw [hh] at H
  exact (zeroOrFullCharacter_smul_iff c hc _).mp H

 theorem vectorWord_basis (j : Fin r) : vectorWord (basis j)=unitWord j := by
  funext i
  simp only [vectorWord,basis,unitWord_apply]
  by_cases h : i=j <;> simp [h,boolEquiv]

/-- Source 7.24, proved in actual support coordinates without postulating a
physical basis-change gadget. The two-basis test is an alternative to the
manuscript's outside-pair proof of the same phase obstruction. -/
theorem source_affine_to_character_radon (hr : 5≤r)
    (f : Signature AlgebraicComplex (2*r)) (hf : Affine f) (hn : f≠0)
    (hd : CFlatSignedRadonCards (fun x => (f (wordVector x):ℂ))) :
    CFlat (fun x => (f x:ℂ)) := by
  obtain ⟨A⟩ := exists_actual_normal_form f hf hn
  have hU := A.direction_selfDual_character (by omega) hd.plus
  obtain ⟨e,he⟩ := exists_support_coordinates (by omega : 0<r) A.direction hU
  obtain ⟨c,Q,hc,hQ⟩ := logicalCoefficient_phase f hf A e
  let s : ℂ := (c:ℂ)*root Q.constant
  have hs : s≠0 := mul_ne_zero (by exact_mod_cast hc) (root_ne_zero _)
  have hp (x : Word r) : (logicalCoefficient f A.shift A.direction e x:ℂ)=s*phase Q x := by
    rw [hQ]
    change (c:ℂ)*root (Q.eval x)=s*phase Q x
    rw [source_phase]
    exact (mul_assoc _ _ _).symm
  have hb (j : Fin r) (l : ZMod 2) : ZeroOrFullCharacter (directionCard Q (basis j) l) := by
    apply logical_phase_cards (by omega) A hd e s hs Q hp
    have hv := support_coordinate_basis_accessible (by omega) A.direction hU e he j
    simpa only [vectorWord_basis,supportEmbedding,LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply] using hv
  let a : Fin r := ⟨0,by omega⟩
  let b : Fin r := ⟨1,by omega⟩
  let k : Fin r := ⟨2,by omega⟩
  have hab : a≠b := by intro H; have := congrArg Fin.val H; simp [a,b] at this
  have hka : k≠a := by intro H; have := congrArg Fin.val H; simp [k,a] at this
  have hkb : k≠b := by intro H; have := congrArg Fin.val H; simp [k,b] at this
  have hm (l : ZMod 2) : ZeroOrFullCharacter (directionCard Q (xor (basis a) (basis b)) l) := by
    apply logical_phase_cards (by omega) A hd e s hs Q hp
    have hv := support_coordinate_pair_accessible (by omega) A.direction hU e he a b hab
    simpa only [vectorWord_xor,vectorWord_basis,supportEmbedding,LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply] using hv
  obtain ⟨ell,hell⟩ := phase_character_of_pair_and_mixed_cards Q
    (pairCards_of_full_directions Q hb) a b k hab hka hkb hm
  right
  apply cFlat_of_logical_character (fun x => (f x:ℂ)) A.shift A.direction hU e
    A.complex_support s hs ell
  intro x
  change (logicalCoefficient f A.shift A.direction e x:ℂ)=s*sign (ell (vectorWord x))
  rw [hp,hell]

end
end Holant.ReedMuller.CharacterRecognition
