import Holant.EightVertex.LocalAffineCollapse.Phase.Support

/-! The only finite checks here inspect words of length four and three explicit
pairings; no affine table or coefficient catalog is assumed or enumerated. -/
namespace Holant.EightVertex.LocalAffineCollapse.Phase
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def zeroWord : W := fun _ => false
def oneWord : W := fun _ => true

def pairedPort : Fin 3 → Fin 4 := ![1, 2, 3]
def otherPort : Fin 3 → Fin 4 := ![2, 1, 1]
def lastPort : Fin 3 → Fin 4 := ![3, 3, 2]

def OnPlane (b : Fin 3) (x : W) : Prop :=
  x 0 = x (pairedPort b) ∧ x (otherPort b) = x (lastPort b)

instance (b : Fin 3) (x : W) : Decidable (OnPlane b x) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem endpoints_onPlane : ∀ b, OnPlane b zeroWord ∧ OnPlane b oneWord := by decide

theorem central_word_plane : ∀ s : W, Holant.weight s % 2 = 0 →
    s ≠ zeroWord → s ≠ oneWord →
    ∃ b : Fin 3, ∀ t : W, Holant.weight t % 2 = 0 → overlap s t % 2 = 0 → OnPlane b t := by
  decide

theorem plane_central_pair : ∀ b : Fin 3, ∀ s t : W,
    OnPlane b s → OnPlane b t → s ≠ zeroWord → s ≠ oneWord →
    t ≠ zeroWord → t ≠ oneWord → t = s ∨ t = complementWord s := by
  decide

theorem plane_weight : ∀ b : Fin 3, ∀ x : W, OnPlane b x →
    Holant.weight x = 2 * ((if x 0 then 1 else 0) + (if x (otherPort b) then 1 else 0)) := by
  decide

theorem complement_one : complementWord oneWord = zeroWord := by decide

theorem support_contained_plane (N : Signature AlgebraicComplex 4)
    (he : ∀ s, N s ≠ 0 → Holant.weight s % 2 = 0)
    (ho : ∀ s t, N s ≠ 0 → N t ≠ 0 → overlap s t % 2 = 0) :
    ∃ b : Fin 3, ∀ x, N x ≠ 0 → OnPlane b x := by
  classical
  by_cases hs : ∃ s, N s ≠ 0 ∧ s ≠ zeroWord ∧ s ≠ oneWord
  · obtain ⟨s, hs, hs0, hs1⟩ := hs
    obtain ⟨b, hb⟩ := central_word_plane s (he s hs) hs0 hs1
    exact ⟨b, fun x hx => hb x (he x hx) (ho s x hs hx)⟩
  · refine ⟨0, ?_⟩
    intro x hx
    have hx' : x = zeroWord ∨ x = oneWord := by
      by_contra hn
      exact hs ⟨x, hx, (not_or.mp hn).1, (not_or.mp hn).2⟩
    rcases hx' with rfl | rfl
    · exact (endpoints_onPlane 0).1
    · exact (endpoints_onPlane 0).2

end
end Holant.EightVertex.LocalAffineCollapse.Phase
