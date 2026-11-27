import Kolberg.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Open problems on the parity of `p n`

These are statements only (`Prop`s), with no proofs: they are open.

* `ParkinShanks`: the odd values of `p n` have natural density `1/2`
  (Parkin–Shanks, 1967).
* `OddPositiveLowerDensity` / `EvenPositiveLowerDensity`: much weaker statements, also open.
-/

open Filter Topology

namespace Kolberg

/-- Number of `n < N` with `p n` odd. -/
def oddCount (N : ℕ) : ℕ := ((Finset.range N).filter (fun n => Odd (p n))).card

/-- Number of `n < N` with `p n` even. -/
def evenCount (N : ℕ) : ℕ := ((Finset.range N).filter (fun n => Even (p n))).card

/-- **Parkin–Shanks conjecture (open).** `p n` is odd for asymptotically half of all `n`. -/
def ParkinShanks : Prop :=
  Tendsto (fun N : ℕ => (oddCount N : ℝ) / N) atTop (𝓝 (1 / 2))

/-- **Open.** The odd values of `p n` have positive lower density. -/
def OddPositiveLowerDensity : Prop :=
  0 < liminf (fun N : ℕ => (oddCount N : ℝ) / N) atTop

/-- **Open.** The even values of `p n` have positive lower density. -/
def EvenPositiveLowerDensity : Prop :=
  0 < liminf (fun N : ℕ => (evenCount N : ℝ) / N) atTop

end Kolberg
