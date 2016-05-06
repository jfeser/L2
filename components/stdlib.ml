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
  if x = [] or y = [] then [] else
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
  if x = 0 then l else
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

let test1 = fun l -> car l
let test2 = if true then 0 else 1
let test3 = fun l1 l2 ->
  if l1 = [] then l2 else
  if l2 = [] then l1 else
    []
