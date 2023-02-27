import tactic                 
import data.set.basic  
import data.real.basic
import algebra.order.floor
import data.real.irrational
import data.set.basic
import data.real.basic
import data.rat.basic


lemma p_is_positive (q : ℝ) (h_q_gt_one : q > 1) : (q / (q - 1)) > 0 :=
begin
  have hq : q - 1 > 0 := by linarith,
  have hqp: q > 0 := by linarith,
  exact div_pos hqp hq,
end