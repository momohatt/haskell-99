(* Reverse-mode Automatic Differentiation *)

let add (x, x') (y, y') =
  fun k ->
  let z = (x +. y, ref 0.0) in
  (k z;
   x' := !x' +. !(snd z);
   y' := !y' +. !(snd z))

let mul (x, x') (y, y') =
  fun k ->
  let z = (x *. y, ref 0.0) in
  (k z;
   x' := !x' +. y *. !(snd z);
   y' := !y' +. x *. !(snd z))

let grad f x =
  let z = (x, ref 0.0) in
  f z (fun (_, r) -> r := 1.0);
  !(snd z)

(* 2x + x^3 *)
let df =
  grad (fun x k ->
      mul (2.0, ref 0.0) x (fun y1 ->
      mul x x (fun y2 ->
      mul y2 x (fun y3 ->
      add y1 y3 k))))

(* x^2 *)
let dg =
  grad (fun x k ->
      mul x x k)
