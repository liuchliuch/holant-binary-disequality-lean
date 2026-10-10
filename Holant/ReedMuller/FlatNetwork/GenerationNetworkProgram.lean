import Holant.ReedMuller.FlatNetwork.GenerationNetworkRM

/-! Every finite generation program is realized by an actual ordinary-port
network. Each transvection adds one literal RM vertex and four I edges;
permutations change boundary incidence only. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GenerationNetwork
variable {n : ℕ}

def applyGate (N : Network ℂ n) : GenerationGate n → Network ℂ n
  | .tau s hs => attachRM N s hs
  | .perm e => reindex N e

theorem allowed_applyGate (N : Network ℂ n) (g : GenerationGate n) (hN : Allowed N) :
    Allowed (applyGate N g) := by
  cases g with
  | tau s hs => exact allowed_attachRM N s hs hN
  | perm e => exact allowed_reindex N e hN

theorem denote_applyGate (N : Network ℂ n) (D : BinaryCode n)
    (hN : N.denote = flatSignature 1 0 D) (g : GenerationGate n) :
    (applyGate N g).denote = flatSignature 1 0 (g.applyCode D) := by
  cases g with
  | tau s hs =>
    funext x
    change (attachRM N s hs).denote x = flatSignature 1 0 (transvectionCode s D) x
    rw [denote_attachRM, hN, flat_zero_value, vector_word, flat_zero_value,
      mem_transvectionCode s (GenerationGate.weightFour_isotropic s hs)]
  | perm e =>
    rw [applyGate, denote_reindex, hN]
    funext x
    change flatSignature 1 0 D (fun i => x (e i)) = flatSignature 1 0 (relabelCode e D) x
    rw [flat_zero_value, flat_zero_value]
    rfl

theorem applyGate_vertices (N : Network ℂ n) (g : GenerationGate n) :
    (applyGate N g).shape.vertices ≤ N.shape.vertices+1 := by
  cases g <;> simp [applyGate]

theorem applyGate_edges (N : Network ℂ n) (g : GenerationGate n) :
    (applyGate N g).shape.edges ≤ N.shape.edges+4 := by
  cases g <;> simp [applyGate]

def realize : GenerationProgram n → Network ℂ n → Network ℂ n
  | [], N => N
  | g :: p, N => applyGate (realize p N) g

theorem allowed_realize (p : GenerationProgram n) (N : Network ℂ n) (hN : Allowed N) :
    Allowed (realize p N) := by
  induction p with
  | nil => exact hN
  | cons g p ih => exact allowed_applyGate _ g ih

theorem denote_realize (p : GenerationProgram n) (N : Network ℂ n) (D : BinaryCode n)
    (hN : N.denote = flatSignature 1 0 D) :
    (realize p N).denote = flatSignature 1 0 (p.run D) := by
  induction p with
  | nil => exact hN
  | cons g p ih => exact denote_applyGate _ _ ih g

theorem realize_vertices (p : GenerationProgram n) (N : Network ℂ n) :
    (realize p N).shape.vertices ≤ N.shape.vertices+p.length := by
  induction p with
  | nil => simp [realize]
  | cons g p ih =>
    have h := applyGate_vertices (realize p N) g
    change (applyGate (realize p N) g).shape.vertices ≤ N.shape.vertices+(p.length+1)
    omega

theorem realize_edges (p : GenerationProgram n) (N : Network ℂ n) :
    (realize p N).shape.edges ≤ N.shape.edges+4*p.length := by
  induction p with
  | nil => simp [realize]
  | cons g p ih =>
    have h := applyGate_edges (realize p N) g
    change (applyGate (realize p N) g).shape.edges ≤ N.shape.edges+4*(p.length+1)
    omega

/-- The complete linear converse, with actual I/RM vertex resources,
actual I/X edges, exact scalar one, and an explicit quadratic graph size. -/
theorem exists_selfDual_network (k : ℕ) (D : BinaryCode (2*k)) (hD : SelfDual D) :
    ∃ N : Network ℂ (2*k), Allowed N ∧ N.denote = flatSignature 1 0 D ∧
      N.shape.vertices ≤ k+4*k^2 ∧ N.shape.edges ≤ 16*k^2 := by
  obtain ⟨p, hp, hb⟩ := selfDual_generation_quadratic k D hD
  have heven : Even (2*k) := even_iff_two_dvd.mpr ⟨k, rfl⟩
  refine ⟨realize p (initial (2*k)), allowed_realize p _ (allowed_initial _ heven), ?_, ?_, ?_⟩
  · rw [denote_realize p _ _ (denote_initial _), hp]
  · have hv := realize_vertices p (initial (2*k))
    rw [initial_vertices _ heven] at hv
    omega
  · have he := realize_edges p (initial (2*k))
    rw [initial_edges] at he
    nlinarith

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
