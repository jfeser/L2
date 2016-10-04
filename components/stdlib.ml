builtin +, -, /, *, %, =, <>, <, <=, >, >=, &&, ||, not, if, ::, car, cdr, tree, value, children

let inf = 4611686018427387903

let rec foldr = fun l f i ->
  if l = [] then i else
    f (foldr (cdr l) f i) (car l)

let rec foldl = fun l f i ->
  if l = [] then i else
    foldl (cdr l) f (f i (car l))

let rec map = fun l f ->
  if l = [] then [] else
    (f (car l)) :: map (cdr l) f

let rec filter = fun l f ->
  if l = [] then [] else
    let rest = filter (cdr l) f in
    if f (car l) then (car l) :: rest else rest

let filteri l f =
  let rec filteri_k l f k =
    if l = [] then [] else
      let rest = filteri_k (cdr l) f (k + 1) in
      if f k (car l) then (car l) :: rest else rest
  in
  filteri_k l f 0

let mapi l f =
  let rec mapi_k l f k =
    if l = [] then [] else
      f k (car l) :: mapi_k (cdr l) f (k + 1)
  in
  mapi_k l f 0

let rec mapt = fun t f ->
  if t = {} then {} else
    tree (f (value t)) (map (children t) (fun c -> mapt c f))

let rec foldt = fun t f i ->
  if t = {} then i else
    f (map (children t) (fun ct -> foldt ct f i)) (value t)

let rec merge = fun x y ->
  if x = [] then y else if y = [] then x else
    let a = car x in
    let b = car y in
    if a < b then a :: (merge (cdr x) y) else b :: (merge x (cdr y))

let rec take = fun l x ->
  if l = [] then [] else
  if x > 0 then (car l) :: (take (cdr l) (x - 1)) else []

let rec zip = fun x y ->
  if x = [] && y = [] then [] else
    [x; y] :: (zip (cdr x) (cdr y))

let rec intersperse = fun l e ->
  if l = [] then [] else
    let xs = cdr l in
    if xs = [] then l else (car l) :: (e :: (intersperse xs e))

let rec append = fun l1 l2 ->
  if l1 = [] then l2 else
  if l2 = [] then l1 else
    (car l1) :: (append (cdr l1) l2)

let rec reverse = fun l ->
  if l = [] then [] else append (reverse (cdr l)) (car l :: [])

let rec concat = fun l ->
  if l = [] then [] else
    append (car l) (concat (cdr l))

let rec drop = fun l x ->
  if x = 0 || l = [] then l else
    drop (cdr l) (x - 1)

let rec sort = fun l ->
  if l = [] then [] else
    let p = car l in
    let lesser = filter (cdr l) (fun e -> e < p) in
    let greater = filter (cdr l) (fun e -> e >= p) in
    append (sort lesser) (p :: (sort greater))

let rec dedup = fun l ->
  if l = [] then [] else
  if (cdr l) = [] then l else
    let sl = sort l in
    let x1 = car sl in
    let x2 = car (cdr sl) in
    if x1 = x2 then dedup (cdr sl) else x1 :: (dedup (cdr sl))

let rec len l =
  if l = [] then 0 else 1 + (len (cdr l))

let nth l n = car (drop l n)

let rec exists l x =
  if l = [] then false else
  if x = (car l) then true else
    exists (cdr l) x

let split_n l n = [take l n; drop l n]

let rec unzip l =
  if l = [] then [[]; []] else
    let hd = car l in
    let hd1 = car hd in
    let hd2 = car (cdr hd) in
    let tl = unzip (cdr l) in
    let tl1 = car tl in
    let tl2 = car (cdr tl) in
    [hd1::tl1; hd2::tl2]

let last l = car (reverse l)

let rec count l x =
  if l = [] then 0 else
  if car l = x then
    1 + (count (cdr l) x)
  else
    count (cdr l) x

let range n =
  let rec range_k k =
    if k >= n then [] else
      k :: (range_k (k + 1))
  in
  range_k 0

let sub l pos len = take (drop l pos) len

let is_empty l = l = []

let rec list_and l =
  if l = [] then true else
    (car l) && (list_and (cdr l))

let rec list_or l =
  if l = [] then false else
    (car l) || (list_or (cdr l))

let rec repeat x n =
  if n = 0 then [] else
    x :: (repeat x (n - 1))

let rec delete_first l x =
  if l = [] then [] else
  if (car l) = x then cdr l else
    (car l) :: (delete_first (cdr l) x)

let rec delete_all l x =
  if l = [] then [] else
  if (car l) = x then delete_all (cdr l) x else
    (car l) :: (delete_all (cdr l) x)

let rec union l1 l2 = dedup (append l1 l2)

let rec intersect l1 l2 =
  if l1 = [] then [] else if l2 = [] then [] else
    let x = car l1 in
    if exists l2 x then
      x :: (intersect (delete_all l1 x) l2)
    else
      intersect (delete_all l1 x) l2

let rec replace l x y =
  if l = [] then [] else
  if (car l) = x then
    y :: (replace (cdr l) x y)
  else
    (car l) :: (replace (cdr l) x y)

(** Int list functions *)
let rec sum x =
  if x = [] then 0 else (car x) + (sum (cdr x))
                                  
let mean x = (sum x) / (len x)
  
let median x =
  car (drop (sort x) ((len x) / 2))

let min x = car (sort x)

let max x = car (reverse (sort x))

let rec product x =
  if x = [] then 1 else
    (car x) * (product (cdr x))

(** Integer functions. *)
let rec pow = fun x y ->
  if y = 0 then 1 else x * (pow x (y - 1))

let neg = fun x -> -1 * x

let fact x =
  if x = 0 then 1 else x * (fact (x - 1))

let abs x =
  if x < 0 then (-1) * x else x

let even x = x % 2 = 0
let odd x = not (even x)
