import Holant.Certificates.NormalizedDihedralQ6.Projection

namespace Holant.Certificates.NormalizedDihedralQ6
set_option maxRecDepth 200000
set_option maxHeartbeats 10000000

/-- The displayed normalized sector-zero words are literal six-coordinate words. -/
theorem standard_sector : ∀ z w : Bool, sectorWord false standard z w = ![z,z,w,w,z,z] := by decide

/-- Original residual fixed/varying edges are distinct, increasing, and cover all residual ports. -/
theorem residual_edges : ∀ e : Fin 6,
    (fixedEdge e).1 < (fixedEdge e).2 ∧ (varyingEdge e).1 < (varyingEdge e).2 ∧
    [((fixedEdge e).1),((fixedEdge e).2),((varyingEdge e).1),((varyingEdge e).2)].Nodup ∧
    ∀ i : Port, i ∈ [((fixedEdge e).1),((fixedEdge e).2),((varyingEdge e).1),((varyingEdge e).2)] ↔ 2 ≤ i.val := by decide

/-- No residual edge choice is omitted or counted twice. -/
theorem fixedEdge_injective : Function.Injective fixedEdge := by decide

theorem fixedEdge_complete : ∀ u v : Port, 2 ≤ u.val → u < v →
    ∃! e : Fin 6, fixedEdge e = (u,v) := by
  have hex : ∀ u v : Port, 2 ≤ u.val → u < v → ∃ e : Fin 6, fixedEdge e = (u,v) := by decide
  intro u v hu huv
  rcases hex u v hu huv with ⟨e,he⟩
  exact ⟨e,he,fun f hf => fixedEdge_injective (hf.trans he.symm)⟩

/-- Exact equations of each sector, in the source's increasing endpoint conventions. -/
theorem sector_equations : ∀ ε : Bool, ∀ d : Sector, ∀ z w : Bool,
    (sectorWord ε d z w) 0 = z ∧ (sectorWord ε d z w) 1 = (z ^^ ε) ∧
    (sectorWord ε d z w) (fixedEdge d.1).1 = w ∧
    (sectorWord ε d z w) (fixedEdge d.1).2 = (w ^^ d.2.1) ∧
    (sectorWord ε d z w) (varyingEdge d.1).1 = (d.2.2.2 ^^ z) ∧
    (sectorWord ε d z w) (varyingEdge d.1).2 = (d.2.2.2 ^^ z ^^ d.2.2.1) := by decide

def exampleRestriction (x : Word) : Fin 4 → Bool := ![x 0,x 2,x 4,x 5]

/-- The manuscript's e=35,(a,b,o)=010 example, on ports(1,3,5,6). -/
theorem printed_example :
    ((slice (canonicalSupport (1,false,true,false)) (1,3) true).image exampleRestriction) =
      ([![false,false,false,true],![false,true,false,false],![false,true,true,true],
        ![true,false,false,false],![true,false,true,true],![true,true,true,false]] : List (Fin 4 → Bool)).toFinset := by decide

theorem canonical_sector_count : Fintype.card Sector = 48 := by decide

end Holant.Certificates.NormalizedDihedralQ6
