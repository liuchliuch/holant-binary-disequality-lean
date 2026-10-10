import Holant.Platonic.StabilizerErasure.QuadraticColumnPhase

/-! The complete no-correctable-erasure branch of Lemma 9.20, including
the nullary output case. Both Clifford frames, the affine columns, their
rank/nonvanishing, and the genuine quadratic phase are constructed. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

/-- The fixed product of one axis Clifford at each physical port. The
empty tensor product is the identity on the nullary Hilbert space. -/
def physicalAxisClifford : {n : ℕ} → (Fin n → Fin 4) → AnalyticClifford n
  | 0,_ => Program.identity.clifford
  | n+1,p => (physicalAxisProgram p).clifford

/-- Failure at every actual physical port; at output arity zero this is
the empty universal condition. -/
def NoCorrectableErasure : {k n : ℕ} → StabilizerIsometry k n → Prop
  | _,0,_ => True
  | _,n+1,V => ∀r : Fin (n+1),¬Correctable V r

theorem zero_output_logical_arity (V : StabilizerIsometry k 0) : k=0 := by
  have hd : 0=k+V.ancillas := by simpa [BinaryVector] using V.coordinates.finrank_eq
  omega

/-- The full column-normal-form clause from the source, without an assumed
alignment or a supplied quadratic phase. The matrix Mᵀ is `columnLinearMap b`;
the r-th source column m_r is exactly b r. -/
theorem source_no_erasure_column_normal_form (V : StabilizerIsometry k n)
    (h : NoCorrectableErasure V) :
    ∃p : Fin n → Fin 4,∃B : AnalyticClifford k,
      ∃c : BinaryVector n,∃b : Fin n → BinaryVector k,
        ∃a₀ : ℂ,∃Q : QuadraticPhase k,
          (∀r,p r≠0 ∧ b r≠0) ∧ a₀≠0 ∧
          Module.finrank (ZMod 2) (columnLinearMap b).range=k ∧
          ∀z,framedMap V (physicalAxisClifford p) B (ket (wordVector z))=
            (a₀*(fourthRootPhase (Q.eval (wordVector z)) : ℂ)) •
              ket (wordVector (c+columnLinearMap b z)) := by
  cases n with
  | zero =>
    have hk := zero_output_logical_arity V
    subst k
    let p : Fin 0 → Fin 4 := Fin.elim0
    let b : Fin 0 → BinaryVector 0 := Fin.elim0
    let a₀ := V.map (ket (wordVector (0 : BinaryVector 0))) (wordVector 0)
    have he : V.map (ket (wordVector (0 : BinaryVector 0)))=
        a₀ • ket (wordVector 0) :=
      simultaneous_z_column _ _ (fun r => Fin.elim0 r)
    have ha : a₀≠0 := by
      intro hz
      have hv : V.map (ket (wordVector (0 : BinaryVector 0)))=V.map 0 := by
        rw [he,hz,zero_smul,map_zero]
      exact ket_ne_zero _ (V.injective hv)
    have hm : columnLinearMap b=0 := by ext z r;exact Fin.elim0 r
    refine ⟨p,Program.identity.clifford,0,b,a₀,QuadraticPhase.zero 0,
      (fun r => Fin.elim0 r),ha,?_,?_⟩
    · simp [hm]
    · intro z
      have hz : z=0 := Subsingleton.elim _ _
      subst z
      simpa [framedMap,physicalAxisClifford,Program.clifford,Program.linearEquiv,
        Program.run,Program.inverse,hm] using he
  | succ n =>
    obtain ⟨p,B,c,b,a,hp,ha,hr,he⟩ := no_correctable_affine_columns V h
    obtain ⟨a₀,ha₀,Q,hQ⟩ := framed_column_quadratic_phase V (physicalAxisProgram p).clifford B
      c (columnLinearMap b) a ha he
    exact ⟨p,B,c,b,a₀,Q,hp,ha₀,hr,fun z => by simpa only [physicalAxisClifford,hQ z] using he z⟩

end
end Holant.Platonic.StabilizerErasure
