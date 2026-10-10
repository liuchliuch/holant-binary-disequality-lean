import Holant.ReedMuller.FlatNetwork.OrdinaryNetwork

/-! Replace each paired free stub by a genuine binary vertex. Its first port
is the original boundary occurrence and its second is the original edge end.
This is an incidence bijection; no old edge or vertex is discarded. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

abbrev ExpandedPorts (s : OpenNetworkShape n) :=
  (Σ v : Fin s.vertices,Fin (s.arity v)) ⊕ (Fin s.free × Bool)

def splitPort (s : OpenNetworkShape n) (side : Bool) : OpenPorts s.vertices s.arity s.free → ExpandedPorts s
  | .inl p => .inl p
  | .inr f => .inr (f,side)

theorem splitPort_injective (s : OpenNetworkShape n) (side : Bool) :
    Function.Injective (splitPort s side) := by
  rintro (p|f) (q|g) h <;> simp only [splitPort,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] at h
  · exact congrArg Sum.inl h
  · cases h
  · cases h
  · exact congrArg Sum.inr h.1

def expandedIncidence (s : OpenNetworkShape n) : (Fin n ⊕ (Fin s.edges × Bool)) → ExpandedPorts s
  | .inl j => splitPort s false (s.boundary j)
  | .inr e => splitPort s true (s.ends e)

theorem boundary_end_disjoint (s : OpenNetworkShape n) (j : Fin n) (e : Fin s.edges × Bool) :
    splitPort s false (s.boundary j)≠splitPort s true (s.ends e) := by
  intro h
  cases hb : s.boundary j with
  | inl p =>
    cases he : s.ends e with
    | inl q =>
      rw [hb,he] at h
      have hpq : p=q := Sum.inl.inj h
      subst q
      exact s.ordinary_boundary_not_paired p j hb ⟨e,he⟩
    | inr f => rw [hb,he] at h;cases h
  | inr f =>
    cases he : s.ends e with
    | inl p => rw [hb,he] at h;cases h
    | inr g => rw [hb,he] at h;cases h

theorem expandedIncidence_bijective (s : OpenNetworkShape n) : Function.Bijective (expandedIncidence s) := by
  constructor
  · rintro (j|e) (k|d) h
    · exact congrArg Sum.inl (s.boundary.injective (splitPort_injective s false h))
    · exact False.elim (boundary_end_disjoint s j d h)
    · exact False.elim (boundary_end_disjoint s k e h.symm)
    · exact congrArg Sum.inr (s.ends.injective (splitPort_injective s true h))
  · rintro (p|⟨f,b⟩)
    · by_cases hb : ∃ j,s.boundary j=.inl p
      · obtain ⟨j,hj⟩ := hb
        exact ⟨.inl j,by simp [expandedIncidence,hj,splitPort]⟩
      · have he : ∃ q,s.ends q=.inl p := by
          by_contra he
          exact hb ((s.ordinary_boundary_iff_unpaired p).mpr he)
        obtain ⟨q,hq⟩ := he
        exact ⟨.inr q,by simp [expandedIncidence,hq,splitPort]⟩
    · cases b
      · exact ⟨.inl (s.freeBoundary f),by simp [expandedIncidence,s.free_boundary,splitPort]⟩
      · exact ⟨.inr (s.freeEdge f),by simp [expandedIncidence,s.free_paired,splitPort]⟩

def expandedPorts (s : OpenNetworkShape n) : (Fin n ⊕ (Fin s.edges × Bool)) ≃ ExpandedPorts s :=
  Equiv.ofBijective (expandedIncidence s) (expandedIncidence_bijective s)

@[simp] theorem expandedPorts_boundary (s : OpenNetworkShape n) (j : Fin n) :
    expandedPorts s (.inl j)=splitPort s false (s.boundary j) := rfl
@[simp] theorem expandedPorts_edge (s : OpenNetworkShape n) (e : Fin s.edges × Bool) :
    expandedPorts s (.inr e)=splitPort s true (s.ends e) := rfl

end
end Holant.ReedMuller.FlatNetwork
