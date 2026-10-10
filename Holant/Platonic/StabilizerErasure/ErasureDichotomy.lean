import Holant.Platonic.StabilizerErasure.PhysicalPauli

/-! The exact all-zero versus one signed-axis alternatives for a correctable
stabilizer port, derived from Clifford compression and anticommutation. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem StabilizerIsometry.scalar_nonzero_action (V : StabilizerIsometry k n)
    (P : Pauli n) (c : ℂ) (hn : c≠0)
    (h : ∀f,V.adjoint (P.run (V.map f))=c • f) :
    ∀f,P.run (V.map f)=c • V.map f := by
  rcases V.pauli_compression_or_lift P with hz|⟨Q,hQ⟩
  · have he := congrFun (h (fun _ => 1)) (origin k)
    have hc : c=0 := by simpa [hz] using he.symm
    exact (hn hc).elim
  · intro f
    have he : Q.run f=c • f := by simpa [hQ] using h f
    rw [hQ,he,map_smul]

theorem sitePauli_anticommute (r : Fin (n+1)) (p q : Fin 4)
    (hp : p≠0) (hq : q≠0) (hpq : p≠q) (f : Signature ℂ (n+1)) :
    siteAction r (qubitPauli p) (siteAction r (qubitPauli q) f)=
      -(siteAction r (qubitPauli q) (siteAction r (qubitPauli p) f)) := by
  ext w
  fin_cases p <;> fin_cases q
  all_goals try { exfalso; first | exact hp rfl | exact hq rfl | exact hpq rfl }
  all_goals cases hw : w r <;>
    simp [siteAction,qubitPauli,hw,←mul_assoc,Complex.I_mul_I]

theorem distinct_pauli_scalars_exclusive (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (p q : Fin 4) (hp : p≠0) (hq : q≠0) (hpq : p≠q)
    (a b : ℂ)
    (ha : ∀f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=a • f)
    (hb : ∀f,V.adjoint (siteAction r (qubitPauli q) (V.map f))=b • f) : a=0 ∨ b=0 := by
  by_contra h
  have hn : a≠0 ∧ b≠0 := by simpa using h
  have ea := V.scalar_nonzero_action (physicalPauli r p) a hn.1
    (by simpa only [physicalPauli_exact] using ha)
  have eb := V.scalar_nonzero_action (physicalPauli r q) b hn.2
    (by simpa only [physicalPauli_exact] using hb)
  simp only [physicalPauli_exact] at ea eb
  have hz : V.map (fun _ => 1)=0 := by
    ext w
    have he := congrFun (sitePauli_anticommute r p q hp hq hpq (V.map (fun _ => 1))) w
    rw [eb,ea,map_smul,map_smul,ea,eb] at he
    simp only [Pi.smul_apply,smul_eq_mul,Pi.neg_apply] at he
    have he0 : (2*a*b)*V.map (fun _ => 1) w=0 := by linear_combination he
    exact (mul_eq_zero.mp he0).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hn.1) hn.2)
  have hi : (fun _ : Word k => (1:ℂ))=0 := V.injective (by simpa using hz)
  have he := congrFun hi (origin k)
  norm_num at he

/-- The three nonidentity expectations are all zero, or exactly one is
nonzero and equals +1 or -1.  This is the source proof's finite marginal
dichotomy, without an assumed stabilizer normal form. -/
theorem correctable_expectation_dichotomy (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : Correctable V r) :
    ∃a : Fin 4 → ℂ,
      (∀p f,V.adjoint (siteAction r (qubitPauli p) (V.map f))=a p • f) ∧
      a 0=1 ∧
      ((∀p,p≠0 → a p=0) ∨
        ∃p,p≠0 ∧ (a p=1 ∨ a p= -1) ∧ ∀q,q≠0 → q≠p → a q=0) := by
  choose a ha he using correctable_pauli_scalar_values V r h
  refine ⟨a,he,?_,?_⟩
  · have h0 := congrFun (he 0 (fun _ => 1)) (origin k)
    simpa [siteAction_qubitPauli_zero] using h0.symm
  · by_cases hz : ∀p,p≠0 → a p=0
    · exact Or.inl hz
    · right
      push Not at hz
      obtain ⟨p,hp,hn⟩ := hz
      refine ⟨p,hp,(ha p).resolve_left hn,?_⟩
      intro q hq hqp
      exact (distinct_pauli_scalars_exclusive V r p q hp hq (Ne.symm hqp)
        (a p) (a q) (he p) (he q)).resolve_left hn

end
end Holant.Platonic.StabilizerErasure
