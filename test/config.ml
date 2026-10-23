(**
  Configure which tests are run
*)
open Cocotreelo

(** select on which encoding all test cases should be run *)
let all_on_one_encoding = Encoding.Encoding_utils.get_encoding "combi"

let maude_path = "extlib/custom-maude/maude"
