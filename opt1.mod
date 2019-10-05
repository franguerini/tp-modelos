/*********************************************
 * OPL 12.8.0.0 Model
 * Author: franciscoguerini
 * Creation Date: Oct 3, 2019 at 9:06:26 PM
 *********************************************/
 
 /*
	M: numero muy grande
	m: numero muy chico
 */ 
 int M = 10000;
 float m = 0.1;
 
 /*
 *	CODIGOS POSTALES
 */
 {string} COD_POSTAL = ...;
 int CANT_COD_POSTAL = card(COD_POSTAL);
 
 /*
 * Destinos por pasada
 * - Ramas del arbol
 */
 int D_P_P = ...;
 int TIEMPO_PROC_CAJA = ...;
 
 /* 
 	Las estaciones son nodos del arbol:
 	
	Calculo el rango de la sumatoria para las estaciones
*/
 range rangoSumaEstaciones = 1..ftoi(ceil((CANT_COD_POSTAL-1) / (D_P_P -1 ) ));
 
 /*
	Calculo cantidad de estaciones
*/
 int cantEstaciones = ftoi((sum(i in rangoSumaEstaciones) D_P_P ^ i) + 1);
 
 range ESTACIONES = 0..(cantEstaciones-1);

  /* 
 	Mismo rango de estaciones pero sin raiz para algunos calculos
 */
  range ESTACIONES_SIN_RAIZ = 1..(cantEstaciones-1);
 
 
   /* 
	Rango para recorrer la cantidad de hermanos que tiene un nodo
   */
 range RANGO_CANT_HERMANOS_POR_NODO = 0..(D_P_P - 1); 
 
   /* 
 	Rango para recorrer todos los grupos de hermanos que hay en el arbol
 */
 range ESTACIONES_HERMANAS = 0..(ftoi(floor(cantEstaciones/D_P_P)) - 1);
    
 /*
 	Estaciones con un solo elemento
	1: La estacion n tiene un solo elemento
	0: En otro caso
 	Esto es para simular que no se siga pasando los elementos a los hijos
 */
 dvar int estacion_con_un_solo_cp[ESTACIONES] in 0..1;
 
 /*
 	Indicadoras de las estaciones
 	1: si tienen elementos
 	0: si no tienen elementos
 */
  dvar int y_estacion[ESTACIONES] in 0..1;
  
 /*
	Matriz que guarda las indicadoras de cuales son los codigos postales que se tienen por estacion
 */
 dvar int codigos_postales_en_estacion[ESTACIONES][COD_POSTAL] in 0..1;

 int CANT_CAJAS[COD_POSTAL] = ...;
 
 /*
 	Arreglo que pasandole un nodo te devuelve el padre
 */
 int IndicePadre[i in ESTACIONES] = i > 0 ? ftoi(floor((i - 1) / D_P_P)) : 0;
 
 /*
 	Matriz con los distintos grupos de hermanos
 	Si se le pasa una estacion devuelve sus hermanos
 */
 int indiceHermanos[i in ESTACIONES_HERMANAS][j in RANGO_CANT_HERMANOS_POR_NODO] = (i*D_P_P) + 1 + j;


  /*
 	Funcion que recibe una estacion y devuelve la cantidad de codigos postales que tiene la estacion
  */
 dexpr int SumaCodigosPostalesEnEstacion[estacion in ESTACIONES] = sum(cod_postal in COD_POSTAL) codigos_postales_en_estacion[estacion][cod_postal];
 
   /*
   Funcion que devuelve si la estacion tiene ese codigo postal
   1: la estacion n tiene el cp
   0: la estacion n no tiene el cp
  */
 dexpr int estacionTieneCodPostal[estacion in ESTACIONES][cod_postal in COD_POSTAL] = codigos_postales_en_estacion[estacion][cod_postal];
 
  /*
 	Funcion que recibe un grupo de hermanos y devuelve la cantidad de codigos postales que tiene el grupo
  */
 dexpr int SumaCodigosPostalesDeHermanos[estacion in ESTACIONES_HERMANAS][hermano in RANGO_CANT_HERMANOS_POR_NODO] = sum(hermano in RANGO_CANT_HERMANOS_POR_NODO) SumaCodigosPostalesEnEstacion[indiceHermanos[estacion][hermano]];

  /*
 	Funcion objetivo
 	Minimizar la suma de los elementos de cada estacion * Cant de cajas
  */
 
 minimize sum(estacion in ESTACIONES, cod_postal in COD_POSTAL) (codigos_postales_en_estacion[estacion][cod_postal] * CANT_CAJAS[cod_postal] * TIEMPO_PROC_CAJA) - sum(cod_postal in COD_POSTAL) (CANT_CAJAS[cod_postal] * TIEMPO_PROC_CAJA); 

 subject to {
 	/*
 		Inicializar la primera estacion con unos.
 		Todos los codigos postales estan en la primer estacion
 	*/
 	forall(cp in COD_POSTAL) {
 		primera_estacion_tiene_todos_los_CP: codigos_postales_en_estacion[0][cp] == 1;
 	}
 	
 	/*
 		Las estaciones hermanas tienen que tener a lo sumo la misma cantidad de elementos que el padre
 		
 		Y ademas
 		
		Control para que el modelo no minimice todo violentamente
		Si no estubiesen estas restricciones el modelo le pondira a las estaciones los menores valores posibles
		- Solo se admite que tome valores minimos si la estacion padre esta muerta (el padre tiene un solo elemento)
		Si la estacion padre no esta muerta, obliga a la estacion a tener exactamente la cantidad de elementos del padre menos los hermanos haciendo que se iguale la restriccion estaciones_hermanas_menor_o_igual_al_padre 	
 	*/
 	 forall(estacion in ESTACIONES_HERMANAS, hermano in RANGO_CANT_HERMANOS_POR_NODO) {
 		estaciones_hermanas_menor_o_igual_al_padre: SumaCodigosPostalesDeHermanos[estacion][hermano] <= SumaCodigosPostalesEnEstacion[IndicePadre[indiceHermanos[estacion][hermano]]]; 
 	 	estaciones_hermanas_padre_muerto_quedan_con_0_elementos: SumaCodigosPostalesDeHermanos[estacion][hermano] >= SumaCodigosPostalesEnEstacion[IndicePadre[indiceHermanos[estacion][hermano]]] - (M * estacion_con_un_solo_cp[IndicePadre[indiceHermanos[estacion][hermano]]]);
 	}
 
	 /*
	 	Se le da valor a las indicadoras, si la estacion tiene al menos un codigo postal
	 	y * m <= variable <= y * M
	 */
	forall(estacion in ESTACIONES) {
 		identficadora_estaciones_inf: y_estacion[estacion] * m <= SumaCodigosPostalesEnEstacion[estacion];
 		identficadora_estaciones_sup: y_estacion[estacion] * M >= SumaCodigosPostalesEnEstacion[estacion];
 	}
 	
 	/*
	 	Esta condicion es necesaria para validar que estacion_con_un_solo_cp este prendida cuando se tiene al menos un elemento en la estacion
	*/
  	forall(n in ESTACIONES) {
 		estacion_con_un_solo_cp_menor_a_identificadora: estacion_con_un_solo_cp[n] <= y_estacion[n];
 	}

 	/*
 		Prendo la variable: estacion_con_un_solo_cp
 		2 * (y_estacion_i - estacion_con_un_solo_cp_i) <= estacion_i <= (1 + (1 - estacion_con_un_solo_cp_i) * M)
 	*/
 	forall(n in ESTACIONES) {
 	 	estacion_muere_inf: 2 * (y_estacion[n] - estacion_con_un_solo_cp[n]) <= SumaCodigosPostalesEnEstacion[n];
 		estacion_muere_sup: SumaCodigosPostalesEnEstacion[n] <= ((1 - estacion_con_un_solo_cp[n]) * M) + 1;
 	}
 	
	/* 
		- El hijo puede tener solo elementos qeu tenia el padre
	*/
	forall(n in ESTACIONES_SIN_RAIZ, cp in COD_POSTAL) {
 		los_hijos_solo_pueden_tener_elementos_del_padre: codigos_postales_en_estacion[n][cp] <= codigos_postales_en_estacion[IndicePadre[n]][cp];
	} 	
	
	/*
		- Las estaciones hermanas no pueden tener los mismo elementos 

	*/
	 forall(estacion in ESTACIONES_HERMANAS, cp in COD_POSTAL) {
 		hermanas_no_pueden_tener_los_mismos_elementos: sum( hermano in RANGO_CANT_HERMANOS_POR_NODO) estacionTieneCodPostal[indiceHermanos[estacion][hermano]][cp] <= 1;
 	}
	
 	/*
 		La cantidad de estaciones muertas tiene que ser igual a la cantidad de elementos que salen de la estacion_1
 	*/
 	cant_muertas: SumaCodigosPostalesEnEstacion[0] == sum(n in ESTACIONES) estacion_con_un_solo_cp[n]; 
 	
 }