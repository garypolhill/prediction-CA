extensions [table]

globals [

  n-rule           ; number of CA transition functions for number of cell states and radius
  n-sync           ; number of combinations of data cell orderings
  n-data           ; number of 'data' patches in each row
  n-sync-data      ; number of patches to compute orderings over (n-data + 2 * radius)
  sample-order?    ; is the combination of orderings to be sampled randomly (as opposed to exhaustively explored)

  data-min-pxcor   ; x co-ordinate of first data patch on each row
  data-max-pxcor   ; x co-ordinate of last data patch on each row

  rule-sample      ; sample of rules being explored (if not all of them)
  eliminated-rules ; set of rules than have been eliminated
  tolerance        ; tolerance to use to count cell state value proportions as being close to 1 or 0

  last-time        ; time elapsed computing the previous tick

  generation       ; generation number of the GA
  prev-scores      ; scores of the previous generation of the GA
  prev-rule-sample ; previous rule sample
]

patches-own [
  state            ; table of rule -> list of states, with one element per sample of combination of ordering
  data-state       ; for patches used to generate data contains the state from the 'real rule'

  n-zeros          ; number of zeros recorded by all rules and orderings
  n-ones           ; number of ones recorded by all rules and orderings
  n-twos           ; number of twos recorded by all rules and orderings

  prop-zero        ; proportion of zeros
  prop-one         ; proportion of ones
  prop-two         ; proportion of twos

  computed?        ; has the cell's state been computed
]

; {observer} initialize
;
; initialize all the global variables, and the 'data' patches

to initialize
  ca

  ; check parameters that depend on each other
  if data-start-step <= initial-step [
    error (word "data-start-step " data-start-step " must be more than initial-step " initial-step)
  ]
  if data-stop-step < data-start-step [
    error (word "data-stop-step " data-stop-step " must be more than or equal to data-start-step " data-start-step)
  ]

  ; initialize global variables and patches' computed? attribute

  set tolerance 10 ^ log10-tolerance
  set n-rule n-states ^ (n-states ^ ((radius * 2) + 1))
  if rand-rule? [
    set real-rule random n-rule
  ]

  ifelse n-rule <= rule-sample-size [
    set rule-sample n-values n-rule [ i -> i ]
  ]
  [
    set rule-sample n-values rule-sample-size [ random n-rule ]
  ]

  ask patches [
    set computed? false
    set data-state -1
  ]

  let data-patches patches with [pycor = (- data-stop-step) and not influenced-by-edge?]
  set data-min-pxcor min [pxcor] of data-patches
  set data-max-pxcor max [pxcor] of data-patches

  set n-data (1 + data-max-pxcor - data-min-pxcor)
  if n-data > max-data [
    let left-data-offset floor (max-data / 2)
    let right-data-offset (max-data mod 2) + (floor (max-data / 2)) - 1
    set data-min-pxcor min-pxcor + (floor (world-width / 2)) - left-data-offset
    set data-max-pxcor min-pxcor + (floor (world-width / 2)) + right-data-offset
    set n-data (1 + data-max-pxcor - data-min-pxcor)
  ]
  set n-sync-data n-data + (2 * radius)

  set n-sync 1
  set sample-order? true
  if not synchronize? [
    set n-sync reduce * n-values n-sync-data [ i -> i + 1 ] ; Computes n-sync-data factorial
    if n-sync > order-sample-size [
      set n-sync order-sample-size
      set sample-order? false
    ]
  ]

  set eliminated-rules table:make

  set last-time 0
  set generation 0
  set prev-scores []

  ; randomly sample the state of row 0

  ask patches with [pycor = 0] [
    set state table:make

    let init-state ifelse-value (random-float 1 < p-zero) [0] [
      ifelse-value (n-states = 2 or random-float 1 < (1 - p-zero) / 2) [1] [2]
    ]

    table:put state real-rule (list init-state)
    set data-state init-state

    set computed? true
    visualize
  ]

  ; compute the 'data' states using the real-rule

  foreach n-values data-stop-step [ i -> -1 - i ] [ ytick ->

    ask patches with [pycor = ytick] [
      let local-state []
      foreach n-values ((2 * radius) + 1) [ i -> i - radius ] [ x ->
        let y pycor + 1
        let nbr-state [data-state] of patch (pxcor + x) pycor
        if x != 0 and (not synchronize?) and nbr-state != -1 [
          set y pycor
        ]
        set local-state lput ([data-state] of patch (pxcor + x) y) local-state
      ]
      set data-state calc-state real-rule local-state
      visualize
    ]
  ]

  ; set the state of the initial-step patches to be that sampled

  ask patches with [(- pycor) <= initial-step and pycor < 0] [
    set state table:make
    foreach rule-sample [ rule ->
      table:put state rule (n-values n-sync [data-state])
    ]
    set computed? true
  ]

  reset-ticks
end

; {observer} reset
;
; Take the state of the simulation back to before any 'go' was executed

to reset
  clear-all-plots
  table:clear eliminated-rules
  set last-time 0

  ask patches with [pycor < 0] [
    ifelse (- pycor) <= initial-step [
      table:clear state
      foreach rule-sample [ rule ->
        table:put state rule (n-values n-sync [data-state])
      ]
      set computed? true
    ] [
      set prop-zero 0
      set prop-one 0
      set prop-two 0
      set computed? false
      set state 0

      set pcolor black
    ]
  ]

  reset-ticks
end

; {any} resample-rules
;
; Resample the set of rules. Should be called before 'reset'

to resample-rules
  ifelse ga? and rule-sample-size < n-rule [
    ; 'breed' the last rules sampled according to how well they did
    ; the more data patches for which a rule matched the output
    ; for more orderings (if asynchronous), the better it did
    let scores table:make
    foreach rule-sample [ rule ->
      table:put scores rule score rule
    ]
    set prev-scores table:values scores
    let pool sort-by [ [rule1 rule2] -> table:get scores rule1 > table:get scores rule2 ] rule-sample

    set prev-rule-sample rule-sample
    set rule-sample []
    let tickets reduce [ [ l n ] -> ifelse-value (is-list? l) [lput (n + last l) l] [(list l (n + l))] ] n-values rule-sample-size [i -> rule-sample-size - i]
    while [length rule-sample < rule-sample-size] [
      let parent1 item (choose-parent tickets) pool
      set tickets remove-ticket parent1 tickets
      let parent2 item (choose-parent tickets) pool
      set tickets remove-ticket parent2 tickets

      let children cross-over parent1 parent2

      foreach children [ child ->
        set rule-sample lput (mutate child) rule-sample
      ]
    ]
  ] [
    ifelse n-rule <= rule-sample-size [
      set rule-sample n-values n-rule [ i -> i ]
    ]
    [
      set rule-sample n-values rule-sample-size [ random n-rule ]
    ]
  ]
end

; {observer} go
;
; Compute the next states of the 1D cellular automaton

to go
  ; advance until we are past the initial-step
  while [ticks < initial-step] [
    tick
  ]

  tick

  ; stop if all rules are eliminated, if the real rule has been eliminated, or if we've run out of space
  if (- ticks) < min-pycor or (table:length eliminated-rules = length (remove-duplicates rule-sample)) or table:has-key? eliminated-rules real-rule [
    stop
  ]

  ; start the timer

  reset-timer

  ; initialize all the patches in this row
  ask patches with [pycor = (- ticks)] [
    set n-zeros 0
    set n-ones 0
    set n-twos 0
    set state table:make
  ]

  ; loop through all the combinations of orderings being sampled...

  foreach (n-values n-sync [ i -> i ]) [ sample ->

    ; ... then through each patch in order as per sample...

    foreach asynch-patches (- ticks) sample [ the-patch ->
      ask the-patch [

        ; ... then through each rule being explored...
        foreach rule-sample [ rule ->

          if not table:has-key? eliminated-rules rule [

            ; ... and compute the state of this patch for the specified ordering
            let local-state []
            foreach n-values ((2 * radius) + 1) [ i -> i - radius ] [ x ->
              let y pycor + 1
              if x != 0 and (not synchronize?) and [computed-sample? rule sample] of patch (pxcor + x) pycor [
                set y pycor
              ]
              set local-state lput ([get-real-state rule sample] of patch (pxcor + x) y) local-state
            ]

            let my-state calc-state rule local-state

            ifelse sample > 0 [
              table:put state rule (lput my-state (table:get state rule))
            ] [
              table:put state rule (list my-state)
            ]

            ; keep track of the number of times each state value has resulted
            (ifelse my-state = 0 [
              set n-zeros n-zeros + 1
            ] my-state = 1 [
              set n-ones n-ones + 1
            ] [
              set n-twos n-twos + 1
            ])

          ]
        ]

      ]
    ]
  ]

  ; housekeeping and rule elimination
  ask patches with [pycor = (- ticks)] [
    let n-rules table:length state
    set prop-zero n-zeros / (n-rules * n-sync)
    set prop-one n-ones / (n-rules * n-sync)
    set prop-two n-twos / (n-rules * n-sync)

    if is-data? [
      foreach rule-sample [ rule ->
        let n-mistake 0
        if table:has-key? state rule [
          foreach table:get state rule [ my-state ->
            if my-state != data-state [
              set n-mistake n-mistake + 1
            ]
          ]
        ]
        if n-mistake = n-sync [
          ; All of the states computed were wrong
          table:put eliminated-rules rule 1
        ]
      ]

    ]
    set computed? true
    visualize
  ]

  ; potentially save memory by allowing state hash to be garbage collected,
  ; but keep the states of each patch up to the first row after data-stop-step
  ; which might be useful after running for exploring rule elimination
  if ticks > data-stop-step + 3 [
    ask patches with [pycor = -2 - ticks] [
      set state 0
    ]
  ]

  set last-time timer
end

; {obs} ga-gen
;
; Perform one generation of the GA

to ga-gen
  if generation > 0 [
    reset
  ]
  while [ticks < data-stop-step and not ((table:length eliminated-rules = length (remove-duplicates rule-sample)) or table:has-key? eliminated-rules real-rule)] [
    go
  ]
  set generation generation + 1
  ifelse table:length eliminated-rules <= max-elim [
    ga-predict
    stop
  ] [
    resample-rules
  ]
end

; {obs} ga-predict
;
; Use the current state of affairs to see what the predictability is

to ga-predict
  while [ticks < (- min-pycor)] [
    go
  ]
end

; {patch} is-data?
;
; Is this a data patch?

to-report is-data?
  report (pxcor >= data-min-pxcor and pxcor <= data-max-pxcor and (- pycor) >= data-start-step and (- pycor) <= data-stop-step)
end

; {patch} computed-sample?
;
; Has this patch computed it's state for the given rule and ordering sample?
; Note that this will throw an error if the patch's state has been set to 0
; to save memory (see 'go'). The 'computed?' attribute is the safe way to check
; this information -- however, this is for use during the calculation of a
; specific row's states

to-report computed-sample? [rule sample]
  report (table:has-key? state rule) and length (table:get state rule) > sample
end

; {observer} aynch-patches
;
; Return a list of patches in row y with the data patches (and the radius either side)
; ordered as per sample.

to-report asynch-patches [y sample]
  if synchronize? [
    ; if the CA is synchronized the order doesn't matter
    report map [ x -> patch x y ] n-values world-width [ x -> x + min-pxcor ]
  ]
  if sample-order? [
    ; if we're not exhaustively exploring all orderings, return a random order
    report shuffle map [ x -> patch x y ] n-values world-width [ x -> x + min-pxcor ]
  ]

  ; get this (i.e. 'sample') ordering of the data patches (plus radius either side)
  ; and 'riffle' them in to a random ordering of the other patches, returning the
  ; result
  let data-patches reorder (map [ x -> patch x y ] n-values n-sync-data [ x -> x + (data-min-pxcor - radius) ]) sample
  let n length data-patches
  let non-data-patches shuffle map [ x -> patch x y ] n-values (world-width - n) [ x -> ifelse-value (x < data-min-pxcor) [x] [x + n] ]
  report riffle data-patches non-data-patches
end

; {any? / obs?} score
;
; Return the score of a rule, which is the number of data patches for which the
; observed data = modelled data for that rule

to-report score [rule]
  let total 0
  foreach n-values n-data [ i -> i + data-min-pxcor ] [ x ->
    foreach n-values (1 + data-stop-step - data-start-step) [ i -> (- i) - data-start-step ] [ y ->
      ask patch x y [
        if not is-number? state and table:has-key? state rule [
          foreach (table:get state rule) [ my-state ->
            if my-state = data-state [
              set total total + 1
            ]
          ]
        ]
      ]
    ]
  ]
  report total
end

; {patch} predictability
;
; Return a string representing the predictability of this patch

to-report predictability
  if (- pycor) < initial-step or ((- pycor) = initial-step and influenced-by-edge?)
    or ((- pycor) >= data-start-step and (- pycor) <= data-stop-step and (pxcor < data-min-pxcor or pxcor > data-max-pxcor)) [
    report "initial"
  ]
  if ((- pycor) = initial-step and not influenced-by-edge?)
    or ((- pycor) >= data-start-step and (- pycor) <= data-stop-step and pxcor >= data-min-pxcor and pxcor <= data-max-pxcor) [
    report "data"
  ]
  if not computed? [
    report "empty"
  ]
  let inv-n-states 1 / n-states
  report ifelse-value (prop-zero < tolerance or prop-one < tolerance or (n-states = 3 and prop-two < tolerance)) [
    ; at least one option is omitted
    ifelse-value (prop-zero > 1 - tolerance or prop-one > 1 - tolerance or prop-two > 1 - tolerance) [
      ; one of the options is present for all rules tested
      "invariable"
    ] [
      ; one ore more options is not present for all rules tested
      "omissive"
    ]
  ] [
    ifelse-value ((abs (prop-zero - inv-n-states)) < tolerance
      and (abs (prop-one - inv-n-states)) < tolerance
      and (n-states = 2 or (abs (prop-two - inv-n-states)) < tolerance)) [
      ; the predicted state by all the rules is (pretty much) equal to 1 / n-states
      "symmetric"
    ] [
      ; there are meaningful differences in the distribution of states across the rules
      "asymmetric"
    ]
  ]
end

; {patch} get-real-state
;
; return the state of this patch for the given rule and sample, unless this is a data patch,
; when the data state (from the real rule) should be returned

to-report get-real-state [rule sample]
  if is-data? [
    report data-state
  ]
  report get-state rule sample
end

; {patch} get-state
;
; return the state of this patch for the given rule and ordering sample, giving meaningful
; error messages if that information is not available for some reason (which would be a bug)

to-report get-state [rule sample]
  if state != 0 and table:has-key? state rule [
    let state-list table:get state rule
    if sample < 0 or sample >= length state-list [
      error (word "Patch at (" pxcor ", " pycor ") has no value for sample " sample " in state of rule " rule)
    ]
    report item sample state-list
  ]
  error (word "Patch at (" pxcor ", " pycor ") has no state for rule " rule)
end

; {patch} influenced-by-edge?
;
; is the patch's state influenced by the edge of the CA?

to-report influenced-by-edge?
  let distance-from-edge min (list (pxcor - min-pxcor) (max-pxcor - pxcor))
  report radius * abs pycor >= distance-from-edge
end

; {any} calc-state
;
; compute the next state given the rule and the local states as a list of states
; in left-to-right order from (- radius) to radius around the patch whose next
; state is being calculated here
;
; the rule is as per Wolfram-numbering (generalized for three-state CA option)

to-report calc-state [rule local-state]
  report item (decimalize local-state) (binarize rule (n-states ^ ((radius * 2) + 1)))
end

; {any} decimalize
;
; Convert a binary (or ternary) list of digits into a decimal number

to-report decimalize [binary]
  let decimal 0
  let bit 0
  foreach reverse binary [ i ->
    set decimal decimal + (i * (n-states ^ bit))

    set bit bit + 1
  ]
  report decimal
end

; {any} binarize
;
; Convert a decimal number into a list of length n-bits with each
; element being the binary (or base 3) digit corresponding to that
; element's index number, with most-significant-bit first

to-report binarize [decimal n-bits]
  let answer []
  let remnant decimal
  foreach n-values n-bits [i -> i + 1] [ i ->
    let bit n-states ^ (n-bits - i)
    ifelse remnant / bit >= 1 [
      ifelse remnant / bit >= 2 [
        set answer lput 2 answer
        set remnant remnant - (2 * bit)
      ]
      [
        set answer lput 1 answer
        set remnant remnant - bit
      ]
    ]
    [
      set answer lput 0 answer
    ]
  ]
  report answer
end

; {any} riffle
;
; Merge two lists together randomly, whilst preserving the order
; of the elements of each argument list in the merged list

to-report riffle [list1 list2]
  let result []
  let n1 length list1
  let n2 length list2
  let n n1 + n2
  let l1 list1
  let l2 list2
  while [n1 > 0 or n2 > 0] [
    ifelse n2 = 0 or random-float n < n1 [
      set result lput (first l1) result
      set l1 but-first l1
      set n1 n1 - 1
    ] [
      set result lput (first l2) result
      set l2 but-first l2
      set n2 n2 - 1
    ]
    set n n - 1
  ]
  report result
end

; {any} reorder
;
; reorder the list in items to be the order-ix'th permutation of the
; (length items) factorial possible permutations of the items in that
; list. Assumes the list doesn't have duplicates.

to-report reorder [items order-ix]
  if length items = 1 [
    report items
  ]
  let pos order-ix mod (length items)
  report insert-item pos (reorder (but-last items) floor (order-ix / (length items))) (last items)
end

; {any} test-reorder
;
; tests that the 'reorder' procedure works. Adjust 'str' according to
; your patience :-)

to test-reorder
  let str "abcdefghi"

  foreach n-values length str [i -> i + 1] [ n ->
    let pass true
    let combos table:make
    let order map [i -> item i str] n-values n [i -> i]

    foreach n-values (reduce * n-values n [i -> i + 1]) [i -> i + 1] [ i ->
      let key reduce word reorder order i
      ifelse table:has-key? combos key [
        set pass false
      ] [
        table:put combos key 1
      ]
    ]
    print (word "n = " n " of " (length str) ": " (ifelse-value pass ["pass"] ["FAIL"]))
  ]
end

; {any} choose-parent
;
; Choose a parent from the breeding pool using a lottery system

to-report choose-parent [tickets]
  let ticket 1 + random last tickets
  report position true map [ i -> i >= ticket ] tickets
end

; {any} remove-ticket
;
; Remove a ticket from a list of tickets given the winner

to-report remove-ticket [winner tickets]
  let subtract n-values (length tickets) [ i -> ifelse-value (i < winner) [0] [1] ]
  let new-tickets (map - tickets subtract)
  while [last new-tickets = 0] [
    set new-tickets but-last new-tickets
  ]
  report new-tickets
end

; {any} cross-over
;
; Report the cross-overs of the two (decimal) rules given as arguments

to-report cross-over [rule1 rule2]
  ifelse random-float 1 < p-crossover [
    let bin1 binarize rule1 (n-states ^ ((radius * 2) + 1))
    let bin2 binarize rule2 (n-states ^ ((radius * 2) + 1))

    let cxp random (1 + length bin1)

    let child1 n-values (length bin1) [ i -> ifelse-value (i >= cxp) [item i bin1] [item i bin2] ]
    let child2 n-values (length bin2) [ i -> ifelse-value (i >= cxp) [item i bin2] [item i bin1] ]

    report (list (decimalize child1) (decimalize child2))
  ] [
    report (list rule1 rule2)
  ]
end

; {any} mutate
;
; Mutate a rule

to-report mutate [rule]
  let bin binarize rule (n-states ^ ((radius * 2) + 1))
  report decimalize n-values (length bin) [ i -> ifelse-value (random-float 1 < p-mutate) [random n-states] [item i bin] ]
end

; {patch} visualize
;
; use the colours on the GUI to show the state of the simulation according
; to the patch's predictability

to visualize
  let prd predictability

  (ifelse (prd = "empty") [
    set pcolor black
  ] (prd = "initial") [
    set pcolor ifelse-value (data-state = 0) [
      ifelse-value (influenced-by-edge?) [zero-colour] [zero-region]
    ] [
      ifelse-value (data-state = 1) [
        ifelse-value (influenced-by-edge?) [one-colour] [one-region]
      ]
      [
        ifelse-value (influenced-by-edge?) [two-colour] [two-region]
      ]
    ]
  ] (prd = "data") [
    set pcolor ifelse-value (data-state = 0) [zero-data] [
      ifelse-value (data-state = 1) [one-data] [two-data]
    ]
  ] [
    let inv-n-states 1 / n-states
    set pcolor ifelse-value (prd = "invariable") [
      ifelse-value (influenced-by-edge?) [invar-col] [
        ifelse-value ((- pycor) > data-stop-step and pxcor >= data-min-pxcor and pxcor <= data-max-pxcor) [invar-data] [invar-reg]
      ]
      ] [ ifelse-value (prd = "omissive") [
        ifelse-value (influenced-by-edge?) [omiss-col] [
          ifelse-value ((- pycor) > data-stop-step and pxcor >= data-min-pxcor and pxcor <= data-max-pxcor) [omiss-data] [omiss-reg]
        ]
        ] [ ifelse-value (prd = "symmetric") [
          ifelse-value (influenced-by-edge?) [sym-col] [
            ifelse-value ((- pycor) > data-stop-step and pxcor >= data-min-pxcor and pxcor <= data-max-pxcor) [sym-data] [sym-reg]
          ]
          ] [ ifelse-value (prd = "asymmetric") [
            ifelse-value (influenced-by-edge?) [asym-col] [
              ifelse-value ((- pycor) > data-stop-step and pxcor >= data-min-pxcor and pxcor <= data-max-pxcor) [asym-data] [asym-reg]
            ]
          ]
          [
            white
          ]
        ]
      ]
    ]
  ])
end
@#$#@#$#@
GRAPHICS-WINDOW
370
86
1581
668
-1
-1
3.0
1
10
1
1
1
0
1
0
1
-200
200
-190
0
0
0
1
ticks
30.0

BUTTON
16
10
90
43
NIL
initialize
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
231
82
366
115
p-zero
p-zero
0
1
0.5
0.001
1
NIL
HORIZONTAL

INPUTBOX
162
336
227
396
one-colour
5.0
1
0
Color

INPUTBOX
162
274
227
334
zero-colour
2.0
1
0
Color

INPUTBOX
230
335
296
395
one-region
115.0
1
0
Color

INPUTBOX
230
273
296
333
zero-region
113.0
1
0
Color

INPUTBOX
93
461
159
521
invar-col
53.0
1
0
Color

INPUTBOX
231
461
296
521
asym-col
23.0
1
0
Color

INPUTBOX
300
461
366
521
sym-col
13.0
1
0
Color

INPUTBOX
93
524
159
584
invar-reg
56.0
1
0
Color

INPUTBOX
300
525
366
585
sym-reg
16.0
1
0
Color

INPUTBOX
231
525
296
585
asym-reg
26.0
1
0
Color

SWITCH
231
47
366
80
synchronize?
synchronize?
0
1
-1000

SLIDER
164
238
366
271
log10-tolerance
log10-tolerance
-20
-1
-6.0
1
1
NIL
HORIZONTAL

BUTTON
16
46
90
79
step
go
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
16
82
90
115
NIL
go
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

MONITOR
1058
10
1139
47
n-invariable
count patches with [pcolor = invar-data]
17
1
9

MONITOR
1058
48
1139
85
n-asymmetrical
count patches with [pcolor = asym-data]
17
1
9

MONITOR
1140
48
1217
85
n-symmetrical
count patches with [pcolor = sym-data]
17
1
9

SLIDER
94
167
229
200
data-start-step
data-start-step
1
50
3.0
1
1
NIL
HORIZONTAL

SLIDER
231
167
366
200
data-stop-step
data-stop-step
1
50
4.0
1
1
NIL
HORIZONTAL

INPUTBOX
300
335
366
395
one-data
105.0
1
0
Color

INPUTBOX
300
273
366
333
zero-data
103.0
1
0
Color

SWITCH
16
202
161
235
rand-rule?
rand-rule?
1
1
-1000

CHOOSER
94
118
229
163
n-states
n-states
2 3
0

INPUTBOX
162
461
228
521
omiss-col
43.0
1
0
Color

INPUTBOX
162
524
228
584
omiss-reg
46.0
1
0
Color

MONITOR
1140
10
1217
47
n-omissive
count patches with [pcolor = omiss-data]
17
1
9

INPUTBOX
300
397
366
457
two-data
108.0
1
0
Color

INPUTBOX
230
397
296
457
two-region
118.0
1
0
Color

INPUTBOX
162
398
227
458
two-colour
8.0
1
0
Color

CHOOSER
231
118
366
163
radius
radius
1 2
0

SLIDER
93
81
228
114
initial-step
initial-step
0
50
2.0
1
1
NIL
HORIZONTAL

INPUTBOX
16
238
160
298
real-rule
110.0
1
0
Number

SLIDER
94
10
230
43
rule-sample-size
rule-sample-size
10
1000
260.0
10
1
NIL
HORIZONTAL

SWITCH
232
10
366
43
ga?
ga?
1
1
-1000

MONITOR
942
20
1044
77
n-eliminated
ifelse-value (is-number? eliminated-rules) [0] [table:length eliminated-rules]
17
1
14

SLIDER
164
202
366
235
max-data
max-data
1
100
5.0
1
1
NIL
HORIZONTAL

INPUTBOX
300
587
367
647
sym-data
18.0
1
0
Color

INPUTBOX
231
587
296
647
asym-data
28.0
1
0
Color

INPUTBOX
161
587
228
647
omiss-data
48.0
1
0
Color

INPUTBOX
93
587
159
647
invar-data
58.0
1
0
Color

SLIDER
94
47
228
80
order-sample-size
order-sample-size
1
1000
750.0
1
1
NIL
HORIZONTAL

PLOT
0
301
160
451
time
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "plot last-time"

BUTTON
16
118
90
151
NIL
reset
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
16
156
90
189
resample
resample-rules
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
624
45
737
78
p-crossover
p-crossover
0
1
0.4
0.01
1
NIL
HORIZONTAL

SLIDER
624
10
737
43
p-mutate
p-mutate
0
1
0.2
0.01
1
NIL
HORIZONTAL

BUTTON
369
10
435
43
NIL
ga-gen
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
369
46
435
79
NIL
ga-gen
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

BUTTON
438
46
511
79
ga-predict
set rule-sample prev-rule-sample\nga-predict
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
514
10
622
43
max-gen
max-gen
10
1000
10.0
10
1
NIL
HORIZONTAL

BUTTON
438
10
511
43
ga-next
repeat max-gen [\n  ga-gen\n]
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
514
45
622
78
max-elim
max-elim
0
100
50.0
1
1
NIL
HORIZONTAL

MONITOR
740
10
828
47
max-score
ifelse-value (is-list? prev-scores and length prev-scores > 0) [max prev-scores] [-1]
17
1
9

MONITOR
740
48
828
85
mean-score
ifelse-value (is-list? prev-scores and length prev-scores > 0) [mean prev-scores] [-1]
2
1
9

MONITOR
835
20
935
77
NIL
generation
17
1
14

@#$#@#$#@
## WHAT IS IT?

This model accompanies thought experiments on prediction in complex systems using 1D cellular automata. The reason for choosing 1D cellular automata is that they are among the simplest models supposedly capable of complex behaviour, with rule 110 (using 'Wolfram numbering') having been proved capable of universal computation (Cook 2004). Rule 110 is a class IV cellular automaton, which are argued to be unpredictable, _except by simulation_ (Wolfram 1983). Though not contradicting that, the model is aimed at asking the following questions:

* Can we recover the rule that generated a sequence of patterns?
* If not, but we have a set of rules that fit a sequence of patterns, what is the _predictability_ of future states of the system?

## HOW IT WORKS

To start with, the model generates a random initial state and runs the 1D cellular automaton forward to generate some data. The model then has to find the rule that generated that data.

The model works by running all the 1D cellular automata rules that match the setup parameters, either exhaustively, or using a randomly selected sample of them, depending on the parameter settings. If the data do not lead to a single rule being identified, the model then runs forward to assess the _predictability_ of future states of the cellular automaton, with cells coloured accordingly:

* _Invariably Predictable_: All rules matching the data agree on the state of the cell. `invar-col`, `invar-reg` and `invar-data` are used to colour them.
* _Omissively Predictable_: There is at least one possible state value that no matching rules have for the cell. This will only happen if there are three or more state values (`n-state` = 3 in the model). `omiss-col`, `omiss-reg` and `omiss-data` are used to colour the cells.
* _Asymmetrically Unpredictable_: Though all of the matching rules between them cover all the possible state values, the number of rules per state value is different. `asym-col`, `asym-reg` and `asym-data` are used to colour the cells.
* _Symmetrically Unpredictable_: The number of matching rules per possible state value is (approximately -- within `log10-tolerance`) equal. This is the worst case scenario in terms of predictability for the cell. `sym-col`, `sym-reg` and `sym-data` are used to colour them.

## HOW TO USE IT

For the simplest setup, use the following parameters (others can be set to whatever you like, and/or have no effect given the settings of these parameters):

* `rule-sample-size` = 260
* `ga?` Off
* `synchronize?` On
* `initial-step` = 2
* `n-states` 2
* `radius` 1
* `data-start-step` = 3
* `data-stop-step` = 3
* `rand-rule?` Off
* `real-rule` = 110
* `max-data` = 5
* `log10-tolerance` = -6

Press `initialize`. The top row of the space will be set to random initial values according to the value of the `p-zero` parameter. Rule 110 (`real-rule`) is then run for two steps (`initial-step`), and five (`max-data`) cells of data collected from step three (`data-start-step` through to `data-stop-step` inclusive). The colours of the cells are according to their state under rule 110:

* Where data are collected, `zero-data` and `one-data` are the colours used for state `0` and `1` respectively.
* Where the states are unaffected by the states of cells at the left or right hand edge of the space `zero-reg` and `one-reg` are the colours used. Although the space wraps-round from left to right, if you were interested in what would happen if the 1D cellular automaton was unbounded, you would ignore the states of cells that were affected by the boundary.
* Otherwise, `zero-col` and `one-reg` are the colours used.

Now press `go`. The model will stop automatically once enough steps to fill the space have been executed. The model will run through all 256 (2^(2^3)) possible rules for a two-state 1D cellular automaton with radius 1, starting at `initial-step`. Typically, at 5, `max-data` will not be large enough for the set of matching rules to be a singleton, and as a consequence, the predictability of the cells after `data-stop-step` will not all be invariable. Various monitors tell you what is going on:

* `n-eliminated`: How many rules have been eliminated. For this setup, we need 255 to be eliminated for there to be a singleton rule.
* `n-invariable`, `n-omissive`, `n-asymmetric` and `n-symmetric` tell you how many cells in the data region have each of the different predictabilities.

Increasing `max-data` (e.g. to 25) or `data-stop-step` (e.g. to 7) is usually enough for 255 of the 256 possible rules to be eliminated.

## THINGS TO NOTICE

The main thing to notice is, as stated above, the numbers of cells with different predictabilities, as recorded by the monitors. The number of eliminated rules is also worth looking at. The model also records the time taken for each step, which, especially if you have set `data-stop-step` to be a reasonable number of steps beyond `data-start-step`, is a way of seeing how the rules being eliminated decreases the time taken for a step.

Another thing to notice, which would be more interesting if the model continued for another several thousand steps, is how the predictability changes the further in time from the `data-stop-step` the 1D cellular automaton runs.

Among the things to try involves using sampling to find the rule rather than exhaustively exploring all the alternatives. This is essential if the `radius` is 2 or `n-states` 3, but if you set `rule-sample-size` to less than 256 with `n-states` 2 and `radius` 1, then not all the 256 possible rules will be explored, but a sample of them. That sample will not necessarily include whatever `real-rule` is set to. With the number of cells in the data sample (which is `(1 + data-stop-step - data-start-step) * max-data`) small enough, it's possible some of the rules in the sample will not be eliminated. The model will still then compute the predictability of the remaining cells based on the rules that match. It's possible that the set of matching rules (not including the `real-rule`) is a singleton, meaning all cells are invariably predictable. Hence the predictability plotted when sampling must be optimistic, and sampling rules with insufficient data can lead to over-confidence.

## THINGS TO TRY

If you're of the view your computer hasn't run enough CPU cycles lately, then by all means play with some of the other settings.

### ASYNCHRONOUS CELLULAR AUTOMATON

Setting `synchronize?` to `Off` implements an asynchronous CA, meaning the state at any one step is no longer deterministic. For the model to try and find the rule, it needs to experiment with all the possible orderings of the `max-data` cells in each step (and `radius` on either side) to find out how well a rule matches. (That's (`max-data` `+` (2 `*` `radius`))! orderings to explore, where '!' is the factorial operator.) If `order-sample-size` is less than the number of possible orderings, these will be sampled rather than explored exhaustively. Rules are eliminated from consideration as asynchronous cellular automaton candidates if they do not match the data under any orderings of cells. If not all orderings are explored then it is possible the `real-rule` would be eliminated.

### INCREASE RADIUS

With a two-state cellular automaton (`n-states` = 2), setting `radius` to 2 increases the number of possible rules to 2^(2^5), or roughly 4.3E9. Exhaustive exploration of all the possible rules is no longer feasible in reasonable time. The `rule-sample-size` parameter is used to choose how many randomly selected rules will be explored. Obviously the chance of finding the right rule just by random sampling is somewhat remote, but exploring this setting, especially with smaller values for `max-data` and difference between `data-start-step` and `data-stop-step` will give you an idea of how optimistic the predictability can be.

Further, since this space of 1D cellular automata haven't (to my knowledge) been explored, you probably won't want to specify the rule, so switching `rand-rule?` to `On` makes sense. This will choose a random `real-rule` from the four billion or so possible rules, but won't guarantee you have a Class IV rule.

With random sampling of rule space not being likely to bring success, a simple genetic algorithm has been implemented to enable smarter searching of rule space. Switch `ga?` to `On`, and the `rule-sample-size` parameter specifies the size of the population the genetic algorithm will maintain. `p-crossover` and `p-mutate` specify the probabilities of genetic operators being applied to the population as it is bred; more successful members of the population have a higher probability of breeding than less successful ones. Success is measured by the number of data points the rule got right.

To run the genetic algorithm, press one of the `ga-gen` buttons, or set `max-gen` to the number of generations you want to run for, and press `ga-next`. The genetic algorithm stops when fewer than `max-elim` rules in the population are 'eliminated' (i.e. they have less than the maximum possible score -- so we know they are wrong -- however this doesn't mean, from a genetic algorithm point of view, that 'eliminated' rules have zero chance of breeding; hence the scare quotes). When the genetic algorithm stops, it automatically uses the population to check the predictability. You can make this happen at any time using the `ga-predict` button.

### THREE-STATE CELLULAR AUTOMATON

If you set `n-states` to 3, then instead of each cell having states 0 or 1, they can also have state 2. This dramatically increases the number of possible rules to 3^(3^3), or roughly 7.6E12. (For the curious, a three-state 1D cellular automaton with radius 2 has 8.7E115 possible rules -- more than the number of atoms in the universe.)

The main reason for including a three-state cellular automaton option is to enable the possibility of having omissively predictable cells. However, the chance of finding the right rule is a thousand times more remote than the two-state cellular automaton with radius 2.

## EXTENDING THE MODEL

Extensions that might be interesting to implement include more intelligent search mechanisms for finding the 'real' transition function, or simply improving the GA.

## CREDITS AND REFERENCES

Cook, M. (2004): [Universality in elementary cellular automata](https://pdfs.semanticscholar.org/12d6/f0bb183050dd78b7671929455b7fdfdf73ce.pdf). Complex Systems 15(1), 1–40 

Wolfram, S. (1983): Cellular Automata. Los Alamos Science 9, 2–21

## LICENCE

                        GNU GENERAL PUBLIC LICENSE
                           Version 3, 29 June 2007

     Copyright (C) 2007 Free Software Foundation, Inc. <http://fsf.org/>
     Everyone is permitted to copy and distribute verbatim copies
     of this license document, but changing it is not allowed.

                                Preamble

      The GNU General Public License is a free, copyleft license for
    software and other kinds of works.

      The licenses for most software and other practical works are designed
    to take away your freedom to share and change the works.  By contrast,
    the GNU General Public License is intended to guarantee your freedom to
    share and change all versions of a program--to make sure it remains free
    software for all its users.  We, the Free Software Foundation, use the
    GNU General Public License for most of our software; it applies also to
    any other work released this way by its authors.  You can apply it to
    your programs, too.

      When we speak of free software, we are referring to freedom, not
    price.  Our General Public Licenses are designed to make sure that you
    have the freedom to distribute copies of free software (and charge for
    them if you wish), that you receive source code or can get it if you
    want it, that you can change the software or use pieces of it in new
    free programs, and that you know you can do these things.

      To protect your rights, we need to prevent others from denying you
    these rights or asking you to surrender the rights.  Therefore, you have
    certain responsibilities if you distribute copies of the software, or if
    you modify it: responsibilities to respect the freedom of others.

      For example, if you distribute copies of such a program, whether
    gratis or for a fee, you must pass on to the recipients the same
    freedoms that you received.  You must make sure that they, too, receive
    or can get the source code.  And you must show them these terms so they
    know their rights.

      Developers that use the GNU GPL protect your rights with two steps:
    (1) assert copyright on the software, and (2) offer you this License
    giving you legal permission to copy, distribute and/or modify it.

      For the developers' and authors' protection, the GPL clearly explains
    that there is no warranty for this free software.  For both users' and
    authors' sake, the GPL requires that modified versions be marked as
    changed, so that their problems will not be attributed erroneously to
    authors of previous versions.

      Some devices are designed to deny users access to install or run
    modified versions of the software inside them, although the manufacturer
    can do so.  This is fundamentally incompatible with the aim of
    protecting users' freedom to change the software.  The systematic
    pattern of such abuse occurs in the area of products for individuals to
    use, which is precisely where it is most unacceptable.  Therefore, we
    have designed this version of the GPL to prohibit the practice for those
    products.  If such problems arise substantially in other domains, we
    stand ready to extend this provision to those domains in future versions
    of the GPL, as needed to protect the freedom of users.

      Finally, every program is threatened constantly by software patents.
    States should not allow patents to restrict development and use of
    software on general-purpose computers, but in those that do, we wish to
    avoid the special danger that patents applied to a free program could
    make it effectively proprietary.  To prevent this, the GPL assures that
    patents cannot be used to render the program non-free.

      The precise terms and conditions for copying, distribution and
    modification follow.

                           TERMS AND CONDITIONS

      0. Definitions.

      "This License" refers to version 3 of the GNU General Public License.

      "Copyright" also means copyright-like laws that apply to other kinds of
    works, such as semiconductor masks.

      "The Program" refers to any copyrightable work licensed under this
    License.  Each licensee is addressed as "you".  "Licensees" and
    "recipients" may be individuals or organizations.

      To "modify" a work means to copy from or adapt all or part of the work
    in a fashion requiring copyright permission, other than the making of an
    exact copy.  The resulting work is called a "modified version" of the
    earlier work or a work "based on" the earlier work.

      A "covered work" means either the unmodified Program or a work based
    on the Program.

      To "propagate" a work means to do anything with it that, without
    permission, would make you directly or secondarily liable for
    infringement under applicable copyright law, except executing it on a
    computer or modifying a private copy.  Propagation includes copying,
    distribution (with or without modification), making available to the
    public, and in some countries other activities as well.

      To "convey" a work means any kind of propagation that enables other
    parties to make or receive copies.  Mere interaction with a user through
    a computer network, with no transfer of a copy, is not conveying.

      An interactive user interface displays "Appropriate Legal Notices"
    to the extent that it includes a convenient and prominently visible
    feature that (1) displays an appropriate copyright notice, and (2)
    tells the user that there is no warranty for the work (except to the
    extent that warranties are provided), that licensees may convey the
    work under this License, and how to view a copy of this License.  If
    the interface presents a list of user commands or options, such as a
    menu, a prominent item in the list meets this criterion.

      1. Source Code.

      The "source code" for a work means the preferred form of the work
    for making modifications to it.  "Object code" means any non-source
    form of a work.

      A "Standard Interface" means an interface that either is an official
    standard defined by a recognized standards body, or, in the case of
    interfaces specified for a particular programming language, one that
    is widely used among developers working in that language.

      The "System Libraries" of an executable work include anything, other
    than the work as a whole, that (a) is included in the normal form of
    packaging a Major Component, but which is not part of that Major
    Component, and (b) serves only to enable use of the work with that
    Major Component, or to implement a Standard Interface for which an
    implementation is available to the public in source code form.  A
    "Major Component", in this context, means a major essential component
    (kernel, window system, and so on) of the specific operating system
    (if any) on which the executable work runs, or a compiler used to
    produce the work, or an object code interpreter used to run it.

      The "Corresponding Source" for a work in object code form means all
    the source code needed to generate, install, and (for an executable
    work) run the object code and to modify the work, including scripts to
    control those activities.  However, it does not include the work's
    System Libraries, or general-purpose tools or generally available free
    programs which are used unmodified in performing those activities but
    which are not part of the work.  For example, Corresponding Source
    includes interface definition files associated with source files for
    the work, and the source code for shared libraries and dynamically
    linked subprograms that the work is specifically designed to require,
    such as by intimate data communication or control flow between those
    subprograms and other parts of the work.

      The Corresponding Source need not include anything that users
    can regenerate automatically from other parts of the Corresponding
    Source.

      The Corresponding Source for a work in source code form is that
    same work.

      2. Basic Permissions.

      All rights granted under this License are granted for the term of
    copyright on the Program, and are irrevocable provided the stated
    conditions are met.  This License explicitly affirms your unlimited
    permission to run the unmodified Program.  The output from running a
    covered work is covered by this License only if the output, given its
    content, constitutes a covered work.  This License acknowledges your
    rights of fair use or other equivalent, as provided by copyright law.

      You may make, run and propagate covered works that you do not
    convey, without conditions so long as your license otherwise remains
    in force.  You may convey covered works to others for the sole purpose
    of having them make modifications exclusively for you, or provide you
    with facilities for running those works, provided that you comply with
    the terms of this License in conveying all material for which you do
    not control copyright.  Those thus making or running the covered works
    for you must do so exclusively on your behalf, under your direction
    and control, on terms that prohibit them from making any copies of
    your copyrighted material outside their relationship with you.

      Conveying under any other circumstances is permitted solely under
    the conditions stated below.  Sublicensing is not allowed; section 10
    makes it unnecessary.

      3. Protecting Users' Legal Rights From Anti-Circumvention Law.

      No covered work shall be deemed part of an effective technological
    measure under any applicable law fulfilling obligations under article
    11 of the WIPO copyright treaty adopted on 20 December 1996, or
    similar laws prohibiting or restricting circumvention of such
    measures.

      When you convey a covered work, you waive any legal power to forbid
    circumvention of technological measures to the extent such circumvention
    is effected by exercising rights under this License with respect to
    the covered work, and you disclaim any intention to limit operation or
    modification of the work as a means of enforcing, against the work's
    users, your or third parties' legal rights to forbid circumvention of
    technological measures.

      4. Conveying Verbatim Copies.

      You may convey verbatim copies of the Program's source code as you
    receive it, in any medium, provided that you conspicuously and
    appropriately publish on each copy an appropriate copyright notice;
    keep intact all notices stating that this License and any
    non-permissive terms added in accord with section 7 apply to the code;
    keep intact all notices of the absence of any warranty; and give all
    recipients a copy of this License along with the Program.

      You may charge any price or no price for each copy that you convey,
    and you may offer support or warranty protection for a fee.

      5. Conveying Modified Source Versions.

      You may convey a work based on the Program, or the modifications to
    produce it from the Program, in the form of source code under the
    terms of section 4, provided that you also meet all of these conditions:

        a) The work must carry prominent notices stating that you modified
        it, and giving a relevant date.

        b) The work must carry prominent notices stating that it is
        released under this License and any conditions added under section
        7.  This requirement modifies the requirement in section 4 to
        "keep intact all notices".

        c) You must license the entire work, as a whole, under this
        License to anyone who comes into possession of a copy.  This
        License will therefore apply, along with any applicable section 7
        additional terms, to the whole of the work, and all its parts,
        regardless of how they are packaged.  This License gives no
        permission to license the work in any other way, but it does not
        invalidate such permission if you have separately received it.

        d) If the work has interactive user interfaces, each must display
        Appropriate Legal Notices; however, if the Program has interactive
        interfaces that do not display Appropriate Legal Notices, your
        work need not make them do so.

      A compilation of a covered work with other separate and independent
    works, which are not by their nature extensions of the covered work,
    and which are not combined with it such as to form a larger program,
    in or on a volume of a storage or distribution medium, is called an
    "aggregate" if the compilation and its resulting copyright are not
    used to limit the access or legal rights of the compilation's users
    beyond what the individual works permit.  Inclusion of a covered work
    in an aggregate does not cause this License to apply to the other
    parts of the aggregate.

      6. Conveying Non-Source Forms.

      You may convey a covered work in object code form under the terms
    of sections 4 and 5, provided that you also convey the
    machine-readable Corresponding Source under the terms of this License,
    in one of these ways:

        a) Convey the object code in, or embodied in, a physical product
        (including a physical distribution medium), accompanied by the
        Corresponding Source fixed on a durable physical medium
        customarily used for software interchange.

        b) Convey the object code in, or embodied in, a physical product
        (including a physical distribution medium), accompanied by a
        written offer, valid for at least three years and valid for as
        long as you offer spare parts or customer support for that product
        model, to give anyone who possesses the object code either (1) a
        copy of the Corresponding Source for all the software in the
        product that is covered by this License, on a durable physical
        medium customarily used for software interchange, for a price no
        more than your reasonable cost of physically performing this
        conveying of source, or (2) access to copy the
        Corresponding Source from a network server at no charge.

        c) Convey individual copies of the object code with a copy of the
        written offer to provide the Corresponding Source.  This
        alternative is allowed only occasionally and noncommercially, and
        only if you received the object code with such an offer, in accord
        with subsection 6b.

        d) Convey the object code by offering access from a designated
        place (gratis or for a charge), and offer equivalent access to the
        Corresponding Source in the same way through the same place at no
        further charge.  You need not require recipients to copy the
        Corresponding Source along with the object code.  If the place to
        copy the object code is a network server, the Corresponding Source
        may be on a different server (operated by you or a third party)
        that supports equivalent copying facilities, provided you maintain
        clear directions next to the object code saying where to find the
        Corresponding Source.  Regardless of what server hosts the
        Corresponding Source, you remain obligated to ensure that it is
        available for as long as needed to satisfy these requirements.

        e) Convey the object code using peer-to-peer transmission, provided
        you inform other peers where the object code and Corresponding
        Source of the work are being offered to the general public at no
        charge under subsection 6d.

      A separable portion of the object code, whose source code is excluded
    from the Corresponding Source as a System Library, need not be
    included in conveying the object code work.

      A "User Product" is either (1) a "consumer product", which means any
    tangible personal property which is normally used for personal, family,
    or household purposes, or (2) anything designed or sold for incorporation
    into a dwelling.  In determining whether a product is a consumer product,
    doubtful cases shall be resolved in favor of coverage.  For a particular
    product received by a particular user, "normally used" refers to a
    typical or common use of that class of product, regardless of the status
    of the particular user or of the way in which the particular user
    actually uses, or expects or is expected to use, the product.  A product
    is a consumer product regardless of whether the product has substantial
    commercial, industrial or non-consumer uses, unless such uses represent
    the only significant mode of use of the product.

      "Installation Information" for a User Product means any methods,
    procedures, authorization keys, or other information required to install
    and execute modified versions of a covered work in that User Product from
    a modified version of its Corresponding Source.  The information must
    suffice to ensure that the continued functioning of the modified object
    code is in no case prevented or interfered with solely because
    modification has been made.

      If you convey an object code work under this section in, or with, or
    specifically for use in, a User Product, and the conveying occurs as
    part of a transaction in which the right of possession and use of the
    User Product is transferred to the recipient in perpetuity or for a
    fixed term (regardless of how the transaction is characterized), the
    Corresponding Source conveyed under this section must be accompanied
    by the Installation Information.  But this requirement does not apply
    if neither you nor any third party retains the ability to install
    modified object code on the User Product (for example, the work has
    been installed in ROM).

      The requirement to provide Installation Information does not include a
    requirement to continue to provide support service, warranty, or updates
    for a work that has been modified or installed by the recipient, or for
    the User Product in which it has been modified or installed.  Access to a
    network may be denied when the modification itself materially and
    adversely affects the operation of the network or violates the rules and
    protocols for communication across the network.

      Corresponding Source conveyed, and Installation Information provided,
    in accord with this section must be in a format that is publicly
    documented (and with an implementation available to the public in
    source code form), and must require no special password or key for
    unpacking, reading or copying.

      7. Additional Terms.

      "Additional permissions" are terms that supplement the terms of this
    License by making exceptions from one or more of its conditions.
    Additional permissions that are applicable to the entire Program shall
    be treated as though they were included in this License, to the extent
    that they are valid under applicable law.  If additional permissions
    apply only to part of the Program, that part may be used separately
    under those permissions, but the entire Program remains governed by
    this License without regard to the additional permissions.

      When you convey a copy of a covered work, you may at your option
    remove any additional permissions from that copy, or from any part of
    it.  (Additional permissions may be written to require their own
    removal in certain cases when you modify the work.)  You may place
    additional permissions on material, added by you to a covered work,
    for which you have or can give appropriate copyright permission.

      Notwithstanding any other provision of this License, for material you
    add to a covered work, you may (if authorized by the copyright holders of
    that material) supplement the terms of this License with terms:

        a) Disclaiming warranty or limiting liability differently from the
        terms of sections 15 and 16 of this License; or

        b) Requiring preservation of specified reasonable legal notices or
        author attributions in that material or in the Appropriate Legal
        Notices displayed by works containing it; or

        c) Prohibiting misrepresentation of the origin of that material, or
        requiring that modified versions of such material be marked in
        reasonable ways as different from the original version; or

        d) Limiting the use for publicity purposes of names of licensors or
        authors of the material; or

        e) Declining to grant rights under trademark law for use of some
        trade names, trademarks, or service marks; or

        f) Requiring indemnification of licensors and authors of that
        material by anyone who conveys the material (or modified versions of
        it) with contractual assumptions of liability to the recipient, for
        any liability that these contractual assumptions directly impose on
        those licensors and authors.

      All other non-permissive additional terms are considered "further
    restrictions" within the meaning of section 10.  If the Program as you
    received it, or any part of it, contains a notice stating that it is
    governed by this License along with a term that is a further
    restriction, you may remove that term.  If a license document contains
    a further restriction but permits relicensing or conveying under this
    License, you may add to a covered work material governed by the terms
    of that license document, provided that the further restriction does
    not survive such relicensing or conveying.

      If you add terms to a covered work in accord with this section, you
    must place, in the relevant source files, a statement of the
    additional terms that apply to those files, or a notice indicating
    where to find the applicable terms.

      Additional terms, permissive or non-permissive, may be stated in the
    form of a separately written license, or stated as exceptions;
    the above requirements apply either way.

      8. Termination.

      You may not propagate or modify a covered work except as expressly
    provided under this License.  Any attempt otherwise to propagate or
    modify it is void, and will automatically terminate your rights under
    this License (including any patent licenses granted under the third
    paragraph of section 11).

      However, if you cease all violation of this License, then your
    license from a particular copyright holder is reinstated (a)
    provisionally, unless and until the copyright holder explicitly and
    finally terminates your license, and (b) permanently, if the copyright
    holder fails to notify you of the violation by some reasonable means
    prior to 60 days after the cessation.

      Moreover, your license from a particular copyright holder is
    reinstated permanently if the copyright holder notifies you of the
    violation by some reasonable means, this is the first time you have
    received notice of violation of this License (for any work) from that
    copyright holder, and you cure the violation prior to 30 days after
    your receipt of the notice.

      Termination of your rights under this section does not terminate the
    licenses of parties who have received copies or rights from you under
    this License.  If your rights have been terminated and not permanently
    reinstated, you do not qualify to receive new licenses for the same
    material under section 10.

      9. Acceptance Not Required for Having Copies.

      You are not required to accept this License in order to receive or
    run a copy of the Program.  Ancillary propagation of a covered work
    occurring solely as a consequence of using peer-to-peer transmission
    to receive a copy likewise does not require acceptance.  However,
    nothing other than this License grants you permission to propagate or
    modify any covered work.  These actions infringe copyright if you do
    not accept this License.  Therefore, by modifying or propagating a
    covered work, you indicate your acceptance of this License to do so.

      10. Automatic Licensing of Downstream Recipients.

      Each time you convey a covered work, the recipient automatically
    receives a license from the original licensors, to run, modify and
    propagate that work, subject to this License.  You are not responsible
    for enforcing compliance by third parties with this License.

      An "entity transaction" is a transaction transferring control of an
    organization, or substantially all assets of one, or subdividing an
    organization, or merging organizations.  If propagation of a covered
    work results from an entity transaction, each party to that
    transaction who receives a copy of the work also receives whatever
    licenses to the work the party's predecessor in interest had or could
    give under the previous paragraph, plus a right to possession of the
    Corresponding Source of the work from the predecessor in interest, if
    the predecessor has it or can get it with reasonable efforts.

      You may not impose any further restrictions on the exercise of the
    rights granted or affirmed under this License.  For example, you may
    not impose a license fee, royalty, or other charge for exercise of
    rights granted under this License, and you may not initiate litigation
    (including a cross-claim or counterclaim in a lawsuit) alleging that
    any patent claim is infringed by making, using, selling, offering for
    sale, or importing the Program or any portion of it.

      11. Patents.

      A "contributor" is a copyright holder who authorizes use under this
    License of the Program or a work on which the Program is based.  The
    work thus licensed is called the contributor's "contributor version".

      A contributor's "essential patent claims" are all patent claims
    owned or controlled by the contributor, whether already acquired or
    hereafter acquired, that would be infringed by some manner, permitted
    by this License, of making, using, or selling its contributor version,
    but do not include claims that would be infringed only as a
    consequence of further modification of the contributor version.  For
    purposes of this definition, "control" includes the right to grant
    patent sublicenses in a manner consistent with the requirements of
    this License.

      Each contributor grants you a non-exclusive, worldwide, royalty-free
    patent license under the contributor's essential patent claims, to
    make, use, sell, offer for sale, import and otherwise run, modify and
    propagate the contents of its contributor version.

      In the following three paragraphs, a "patent license" is any express
    agreement or commitment, however denominated, not to enforce a patent
    (such as an express permission to practice a patent or covenant not to
    sue for patent infringement).  To "grant" such a patent license to a
    party means to make such an agreement or commitment not to enforce a
    patent against the party.

      If you convey a covered work, knowingly relying on a patent license,
    and the Corresponding Source of the work is not available for anyone
    to copy, free of charge and under the terms of this License, through a
    publicly available network server or other readily accessible means,
    then you must either (1) cause the Corresponding Source to be so
    available, or (2) arrange to deprive yourself of the benefit of the
    patent license for this particular work, or (3) arrange, in a manner
    consistent with the requirements of this License, to extend the patent
    license to downstream recipients.  "Knowingly relying" means you have
    actual knowledge that, but for the patent license, your conveying the
    covered work in a country, or your recipient's use of the covered work
    in a country, would infringe one or more identifiable patents in that
    country that you have reason to believe are valid.

      If, pursuant to or in connection with a single transaction or
    arrangement, you convey, or propagate by procuring conveyance of, a
    covered work, and grant a patent license to some of the parties
    receiving the covered work authorizing them to use, propagate, modify
    or convey a specific copy of the covered work, then the patent license
    you grant is automatically extended to all recipients of the covered
    work and works based on it.

      A patent license is "discriminatory" if it does not include within
    the scope of its coverage, prohibits the exercise of, or is
    conditioned on the non-exercise of one or more of the rights that are
    specifically granted under this License.  You may not convey a covered
    work if you are a party to an arrangement with a third party that is
    in the business of distributing software, under which you make payment
    to the third party based on the extent of your activity of conveying
    the work, and under which the third party grants, to any of the
    parties who would receive the covered work from you, a discriminatory
    patent license (a) in connection with copies of the covered work
    conveyed by you (or copies made from those copies), or (b) primarily
    for and in connection with specific products or compilations that
    contain the covered work, unless you entered into that arrangement,
    or that patent license was granted, prior to 28 March 2007.

      Nothing in this License shall be construed as excluding or limiting
    any implied license or other defenses to infringement that may
    otherwise be available to you under applicable patent law.

      12. No Surrender of Others' Freedom.

      If conditions are imposed on you (whether by court order, agreement or
    otherwise) that contradict the conditions of this License, they do not
    excuse you from the conditions of this License.  If you cannot convey a
    covered work so as to satisfy simultaneously your obligations under this
    License and any other pertinent obligations, then as a consequence you may
    not convey it at all.  For example, if you agree to terms that obligate you
    to collect a royalty for further conveying from those to whom you convey
    the Program, the only way you could satisfy both those terms and this
    License would be to refrain entirely from conveying the Program.

      13. Use with the GNU Affero General Public License.

      Notwithstanding any other provision of this License, you have
    permission to link or combine any covered work with a work licensed
    under version 3 of the GNU Affero General Public License into a single
    combined work, and to convey the resulting work.  The terms of this
    License will continue to apply to the part which is the covered work,
    but the special requirements of the GNU Affero General Public License,
    section 13, concerning interaction through a network will apply to the
    combination as such.

      14. Revised Versions of this License.

      The Free Software Foundation may publish revised and/or new versions of
    the GNU General Public License from time to time.  Such new versions will
    be similar in spirit to the present version, but may differ in detail to
    address new problems or concerns.

      Each version is given a distinguishing version number.  If the
    Program specifies that a certain numbered version of the GNU General
    Public License "or any later version" applies to it, you have the
    option of following the terms and conditions either of that numbered
    version or of any later version published by the Free Software
    Foundation.  If the Program does not specify a version number of the
    GNU General Public License, you may choose any version ever published
    by the Free Software Foundation.

      If the Program specifies that a proxy can decide which future
    versions of the GNU General Public License can be used, that proxy's
    public statement of acceptance of a version permanently authorizes you
    to choose that version for the Program.

      Later license versions may give you additional or different
    permissions.  However, no additional obligations are imposed on any
    author or copyright holder as a result of your choosing to follow a
    later version.

      15. Disclaimer of Warranty.

      THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY
    APPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT
    HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM "AS IS" WITHOUT WARRANTY
    OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO,
    THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
    PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM
    IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF
    ALL NECESSARY SERVICING, REPAIR OR CORRECTION.

      16. Limitation of Liability.

      IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
    WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS
    THE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY
    GENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE
    USE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF
    DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD
    PARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS),
    EVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
    SUCH DAMAGES.

      17. Interpretation of Sections 15 and 16.

      If the disclaimer of warranty and limitation of liability provided
    above cannot be given local legal effect according to their terms,
    reviewing courts shall apply local law that most closely approximates
    an absolute waiver of all civil liability in connection with the
    Program, unless a warranty or assumption of liability accompanies a
    copy of the Program in return for a fee.

                         END OF TERMS AND CONDITIONS

                How to Apply These Terms to Your New Programs

      If you develop a new program, and you want it to be of the greatest
    possible use to the public, the best way to achieve this is to make it
    free software which everyone can redistribute and change under these terms.

      To do so, attach the following notices to the program.  It is safest
    to attach them to the start of each source file to most effectively
    state the exclusion of warranty; and each file should have at least
    the "copyright" line and a pointer to where the full notice is found.

        <one line to give the program's name and a brief idea of what it does.>
        Copyright (C) <year>  <name of author>

        This program is free software: you can redistribute it and/or modify
        it under the terms of the GNU General Public License as published by
        the Free Software Foundation, either version 3 of the License, or
        (at your option) any later version.

        This program is distributed in the hope that it will be useful,
        but WITHOUT ANY WARRANTY; without even the implied warranty of
        MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
        GNU General Public License for more details.

        You should have received a copy of the GNU General Public License
        along with this program.  If not, see <http://www.gnu.org/licenses/>.

    Also add information on how to contact you by electronic and paper mail.

      If the program does terminal interaction, make it output a short
    notice like this when it starts in an interactive mode:

        <program>  Copyright (C) <year>  <name of author>
        This program comes with ABSOLUTELY NO WARRANTY; for details type `show w'.
        This is free software, and you are welcome to redistribute it
        under certain conditions; type `show c' for details.

    The hypothetical commands `show w' and `show c' should show the appropriate
    parts of the General Public License.  Of course, your program's commands
    might be different; for a GUI interface, you would use an "about box".

      You should also get your employer (if you work as a programmer) or school,
    if any, to sign a "copyright disclaimer" for the program, if necessary.
    For more information on this, and how to apply and follow the GNU GPL, see
    <http://www.gnu.org/licenses/>.

      The GNU General Public License does not permit incorporating your program
    into proprietary programs.  If your program is a subroutine library, you
    may consider it more useful to permit linking proprietary applications with
    the library.  If this is what you want to do, use the GNU Lesser General
    Public License instead of this License.  But first, please read
    <http://www.gnu.org/philosophy/why-not-lgpl.html>.

## ChangeLog

2020-02-26 Gary Polhill

  * Modified `visualize` and `predictability` so that the `initial-step` row not `influenced-by-edge?` would be presented as though it is data -- which, depending on how far ahead the prediction is wanted, it is.

2020-02-24 Gary Polhill

  * First release
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

sheep
false
15
Circle -1 true true 203 65 88
Circle -1 true true 70 65 162
Circle -1 true true 150 105 120
Polygon -7500403 true false 218 120 240 165 255 165 278 120
Circle -7500403 true false 214 72 67
Rectangle -1 true true 164 223 179 298
Polygon -1 true true 45 285 30 285 30 240 15 195 45 210
Circle -1 true true 3 83 150
Rectangle -1 true true 65 221 80 296
Polygon -1 true true 195 285 210 285 210 240 240 210 195 210
Polygon -7500403 true false 276 85 285 105 302 99 294 83
Polygon -7500403 true false 219 85 210 105 193 99 201 83

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

wolf
false
0
Polygon -16777216 true false 253 133 245 131 245 133
Polygon -7500403 true true 2 194 13 197 30 191 38 193 38 205 20 226 20 257 27 265 38 266 40 260 31 253 31 230 60 206 68 198 75 209 66 228 65 243 82 261 84 268 100 267 103 261 77 239 79 231 100 207 98 196 119 201 143 202 160 195 166 210 172 213 173 238 167 251 160 248 154 265 169 264 178 247 186 240 198 260 200 271 217 271 219 262 207 258 195 230 192 198 210 184 227 164 242 144 259 145 284 151 277 141 293 140 299 134 297 127 273 119 270 105
Polygon -7500403 true true -1 195 14 180 36 166 40 153 53 140 82 131 134 133 159 126 188 115 227 108 236 102 238 98 268 86 269 92 281 87 269 103 269 113

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.1.1
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
