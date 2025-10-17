
; Estructuras:
; (robot id pos estado bateria capacidad carga_actual)
; (pedido id zona peso prioridad estado)
; (estanteria id zona nodo)
; (estacion_carga id nodo)
; (politica umbral_bateria)
; (distancia desde hasta valor)
; (tarea_asignada pedido robot)
; (tarea_recarga robot estacion)

; (evento tipo obj) ; tipo: nuevo_pedido | fin_pedido | solicitar_recarga | fin_recarga
; Estos tendran estructura del id 
(deffacts base_inicial

; (politica umbral_bateria)
  (politica 25)

; (estanteria id zona nodo)
  (estanteria sA1 zA n2)
  (estanteria sB1 zB n4)

; (estacion_carga id nodo)
  (estacion_carga c1 n0)
  (estacion_carga c2 n5)

; (distancia desde hasta valor)

  ; distancias a nodo n2 (zona zA)
  (distancia n1 n2 7.5)
  (distancia n2 n2 0.0)
  (distancia n3 n2 6.0)
  (distancia n4 n2 8.0)


  ; distancias a nodo n4 (zona zB)
  (distancia n1 n4 6.8)
  (distancia n2 n4 3.2)
  (distancia n3 n4 5.0)
  (distancia n4 n4 0.0)

  ; distancias a estaciones de carga (n0 y n5)
  (distancia n1 n0 3.0)
  (distancia n3 n0 5.5)
  (distancia n4 n0 2.5)

  (distancia n1 n5 9.0)
  (distancia n3 n5 4.5)
  (distancia n4 n5 3.0)

; (robot id pos estado bateria capacidad carga_actual)
  (robot r1 n1 idle 80 30 0)
  (robot r2 n3 idle 22 25 0) ; Va a saltar bateria baja
  (robot r3 n4 idle 55 15 0)

; (pedido id zona peso prioridad estado)
  (pedido p1 zA 10 normal pendiente)


; Las que se haran con asserts en las reglas:
; (tarea_asignada pedido robot)
; (tarea_recarga robot estacion)


; Las que se haran en la consola en ejecucion simulando solicitudes:
; (evento tipo obj(id)) ; tipo: nuevo_pedido | fin_pedido | solicitar_recarga | fin_recarga
)

; Regla Crear pedido desde evento nuevo_pedido
(defrule crear_pedido_desde_evento
  ?ev <- (evento nuevo_pedido ?pid ?zona ?peso ?prio)
  ; evitar duplicados: si ya existe un pedido con ese id, no crearlo
  (not (pedido ?pid $?prest))
  =>
  (assert (pedido ?pid ?zona ?peso ?prio pendiente))
  (retract ?ev)
  (printout t "[NUEVO] Creado pedido " ?pid " en zona " ?zona " (Peso: " ?peso ", Prioridad: " ?prio ")." crlf)
)

; Regla Asignar robot mas adecuado (idle, bateria >= umbral, capacidad >= peso, mas cercano)
(defrule asignar_robot_mas_adecuado

  (politica ?u)

  ?pf <- (pedido ?pid ?zona ?peso ?prio pendiente)
  (estanteria ?sid ?zona ?nodo_pick)

  ; Robot candidato que se encuentre en estado de espera, 
  ; con mas bateria que la politica y capacidad de peso mayor a la del pedido
  ?rf <- (robot ?rid ?pos idle ?bat ?cap $?resto)
  (test (>= ?cap ?peso))
  (test (>= ?bat ?u))

  ; Se consulta la distancia desde la posicion del robot a 
  ; el nodo de la estanteria que se encuentra en la zona del pedido
  (distancia ?pos ?nodo_pick ?d)

  ; Se comparan todos los robots para ver cual es el mas cercano
  (not (and
        (robot ?rid2 ?pos2 idle ?bat2 ?cap2 $?resto2)
        (test (neq ?rid2 ?rid))
        (test (>= ?cap2 ?peso))
        (test (>= ?bat2 ?u))

        (distancia ?pos2 ?nodo_pick ?d2)
        (test (< ?d2 ?d))
       ))
  =>
  (assert (tarea_asignada ?pid ?rid))

  ; pedido -> en_preparacion
  (retract ?pf)
  (assert (pedido ?pid ?zona ?peso ?prio en_preparacion))

  ; robot -> asignado
  (retract ?rf)
  (assert (robot ?rid ?pos asignado ?bat ?cap $?resto))

  (printout t "[ASIGNACION] Pedido " ?pid " -> robot " ?rid " Distancia: " ?d ")" crlf)
)

; Regla Completar pedido (evento fin_pedido)
(defrule completar_pedido
  ; Se buscan la tarea robot y pedido con mismos ID y que coincidan con el del evento 
  ?ta <- (tarea_asignada ?pid ?rid)
  ?pf <- (pedido ?pid ?zona ?peso ?prio en_preparacion)
  ?rf <- (robot ?rid ?pos asignado ?bat ?cap $?resto)
  ?ev <- (evento fin_pedido ?pid)
  =>
  ; Se establece el estado del pedido a completado y el del robot a en espera y se borra la tarea y el evento
  (retract ?pf)
  (assert (pedido ?pid ?zona ?peso ?prio completado))

  ; Se hace una variable nueva bateria restandole 10 para simular el gasto
  (bind ?nuevo_bat (- ?bat 10))
  (if (< ?nuevo_bat 0) then (bind ?nuevo_bat 0)) ;Evitar numeros negativos

  (retract ?rf)
  (assert (robot ?rid ?pos idle ?nuevo_bat ?cap $?resto))

  (retract ?ta)
  (retract ?ev)

  (printout t "[FIN] Pedido " ?pid " completado. robot " ?rid " -> idle" crlf)
)

; Regla Detectar bateria baja en robots IDLE
(defrule detectar_bateria_baja

  ; Si la bateria esta por debajo del umbral crear evento de recarga con el id del robot
  (politica ?u)
  ?rf <- (robot ?rid ?pos idle ?bat ?cap $?resto)
  (test (< ?bat ?u))
  =>
  (assert (evento solicitar_recarga ?rid))

  (printout t "[ENERGIA] Bateria baja en " ?rid " -> solicitar_recarga" crlf)
)

; Regla Enviar a recarga (elige estacion mas cercana)
(defrule enviar_a_recarga
  ?ev <- (evento solicitar_recarga ?rid)
  ?rf <- (robot ?rid ?pos idle ?bat ?cap $?resto)
  ; Estaciones candidatas
  (estacion_carga ?eid ?enodo)
  (distancia ?pos ?enodo ?d)
  ; Se verifica que se este asignando la estacion mas cercana a la posicion del robot
  (not (and
        (estacion_carga ?eid2 ?enodo2)
        (test (neq ?eid2 ?eid))
        (distancia ?pos ?enodo2 ?d2)
        (test (< ?d2 ?d))
       ))
  =>
  ;Se crea la terea de que esta cargando, se cambia el estado del robot a recargando y se borra el evento
  (assert (tarea_recarga ?rid ?eid))
  (retract ?rf)
  (assert (robot ?rid ?pos recargando ?bat ?cap $?resto))
  (retract ?ev)

  (printout t "[RECARGA] Robot " ?rid " -> estacion " ?eid " Distancia: " ?d "). Estado: recargando" crlf)
)

; Regla Finalizar recarga (evento fin_recarga)
(defrule finalizar_recarga
  ?tr <- (tarea_recarga ?rid ?eid)
  ?rf <- (robot ?rid ?pos recargando ?bat ?cap $?resto)
  ?ev <- (evento fin_recarga ?rid)
  =>
  (retract ?rf)
  (assert (robot ?rid ?pos idle 100 ?cap $?resto))
  (retract ?tr)
  (retract ?ev)
  (printout t "[RECARGA OK] Robot " ?rid " listo. Bateria=100%, Estado: idle" crlf)
)