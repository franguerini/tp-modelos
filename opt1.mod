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
 	Destinos por pasada
 	- Ramas del arbol
 */
 int D_P_P = 2;

 /* 
 	Las estaciones son nodos del arbol
 */
 {int} ESTACIONES = {0, 1, 2, 3, 4, 5, 6};
 
 {int} ESTACIONES_SIN_RAIZ = {1, 2, 3, 4, 5, 6};
  
 /*
 	Estaciones muertas
 	Una estacion esta muerta si tiene solamente 1 elemento
 	Esto es para simular que no se siga pasando los elementos a los hijos
 */
 dvar int estacion_muerta[ESTACIONES] in 0..1;
 
 /*
 	Indicadoras de las estaciones
 	1: si tienen elementos
 	0: si no tienen elementos
 */
  dvar int y_estacion[ESTACIONES] in 0..1;
  
  
 /*
	CODIGOS POSTALES
 */
 {string} COD_POSTAL = {"A", "B", "C"};

 /*
	Matriz que guarda las indicadoras de cuales son los codigos postales que se tienen por estacion
 */
 dvar int codigos_postales_en_estacion[ESTACIONES][COD_POSTAL] in 0..1;

 int CANT_CAJAS[COD_POSTAL] = ...;

  /*
 	Funcion objetivo
 	Minimizar la suma de los elementos de cada estacion * Cant de cajas
  */
  minimize sum(estacion in ESTACIONES, cod_postal in COD_POSTAL) (codigos_postales_en_estacion[estacion][cod_postal] * CANT_CAJAS[cod_postal]); 


  /*
 	Funcion que recibe una estacion y devuelve la cantidad de codigos postales que tiene la estacion
  */
 dexpr int SumaCodigosPostalesEnEstacion[estacion in ESTACIONES] = sum(cod_postal in COD_POSTAL) codigos_postales_en_estacion[estacion][cod_postal];

 int IndicePadre[i in ESTACIONES] = i > 0 ? ftoi(floor((i - 1) / D_P_P)) : 0; 

 subject to {
  
 	/*
 		Inicializar la primera estacion con unos.
 		Todos los codigos postales estan en la primer estacion
 	*/
 	forall(cp in COD_POSTAL) {
 		primera_estacion_tiene_todos_los_CP: codigos_postales_en_estacion[0][cp] == 1;
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
	 	Esta condicion es necesaria para decir que una estacion no esta muerta si no tiene codigos postales
	*/
  	forall(n in ESTACIONES) {
 		estacion_muerta_menor_a_identificadora: estacion_muerta[n] <= y_estacion[n];
 	}
 
 	/*
		La suma de codigos postales de dos estaciones hermanas debe ser menor o igual a la suma de codigos postales del padre
 	*/	 
	or_estacion_2_y_3: SumaCodigosPostalesEnEstacion[1] + SumaCodigosPostalesEnEstacion[2] <= SumaCodigosPostalesEnEstacion[0]; 
	or_estacion_4_y_5: SumaCodigosPostalesEnEstacion[3] + SumaCodigosPostalesEnEstacion[4] <= SumaCodigosPostalesEnEstacion[1]; 
	or_estacion_6_y_7: SumaCodigosPostalesEnEstacion[5] + SumaCodigosPostalesEnEstacion[6] <= SumaCodigosPostalesEnEstacion[2]; 
	
	/*
		Control para que el modelo no minimice todo violentamente
		Si no estubiesen estas restricciones el modelo le pondira a las estaciones los menores valores posibles
		- Solo se admite que tome valores minimos si la estacion padre esta muerta (Anulando la restriccion)
		Si la estacion padre no esta muerta, obliga a la estacion a tener exactamente la cantidad de elementos del padre menos los hermanos 	
 	*/	 	
 	padre_muerto_hijos_0_para_2_3: SumaCodigosPostalesEnEstacion[1] + SumaCodigosPostalesEnEstacion[2] >= SumaCodigosPostalesEnEstacion[0] - (M * estacion_muerta[0]); 
  	padre_muerto_hijos_0_para_4_5: SumaCodigosPostalesEnEstacion[3] + SumaCodigosPostalesEnEstacion[4] >= SumaCodigosPostalesEnEstacion[1] - (M * estacion_muerta[1]); 
  	padre_muerto_hijos_0_para_6_7: SumaCodigosPostalesEnEstacion[5] + SumaCodigosPostalesEnEstacion[6] >= SumaCodigosPostalesEnEstacion[2] - (M * estacion_muerta[2]); 
 	
 	/*
 		Lo que mata a las estaciones
 		Si la estacion tiene un solo elemento entoces la estacion tiene qeu estar muerta
 		2 * (y_estacion_i - estacion_i_muerta) <= estacion_i <= (1 + (1 - estacion_i_muerta) * M)
 	*/
 	forall(n in ESTACIONES) {
 	 	estacion_muere_inf: 2 * (y_estacion[n] - estacion_muerta[n]) <= SumaCodigosPostalesEnEstacion[n];
 		estacion_muere_sup: SumaCodigosPostalesEnEstacion[n] <= ((1 - estacion_muerta[n]) * M) + 1;
 	}
 	
 	
 	/*
 		El hijo tiene que tener un codigo postal del padre
 	*/
 	
  	forall(cp in COD_POSTAL) {
  	/*  	
  	
 		hijo_2_tiene_solo_los_CP_de_1: codigos_postales_en_estacion[2][cp] <= codigos_postales_en_estacion[1][cp];
 		hijo_3_tiene_solo_los_CP_de_1: codigos_postales_en_estacion[3][cp] <= codigos_postales_en_estacion[1][cp];
 		hijo_4_tiene_solo_los_CP_de_2: codigos_postales_en_estacion[4][cp] <= codigos_postales_en_estacion[2][cp];
 		hijo_5_tiene_solo_los_CP_de_2: codigos_postales_en_estacion[5][cp] <= codigos_postales_en_estacion[2][cp];
 		hijo_6_tiene_solo_los_CP_de_3: codigos_postales_en_estacion[6][cp] <= codigos_postales_en_estacion[3][cp];
 		hijo_7_tiene_solo_los_CP_de_3: codigos_postales_en_estacion[7][cp] <= codigos_postales_en_estacion[3][cp];
 		*/
 		
 		hermanos_2_3_no_pueden_tener_los_mismos_cp: codigos_postales_en_estacion[1][cp] + codigos_postales_en_estacion[2][cp] <= 1;
 		hermanos_4_5_no_pueden_tener_los_mismos_cp: codigos_postales_en_estacion[4][cp] + codigos_postales_en_estacion[3][cp] <= 1;
 		hermanos_6_7_no_pueden_tener_los_mismos_cp: codigos_postales_en_estacion[5][cp] + codigos_postales_en_estacion[6][cp] <= 1;
	} 	
	
	forall(n in ESTACIONES_SIN_RAIZ, cp in COD_POSTAL) {
 		hijo_2_tiene_solo_los_CP_de_1: codigos_postales_en_estacion[n][cp] <= codigos_postales_en_estacion[IndicePadre[n]][cp];
	} 	
	
 	
 	/*
 		La cantidad de estaciones muertas tiene que ser igual a la cantidad de elementos que salen de la estacion_1
 	*/
 	cant_muertas: SumaCodigosPostalesEnEstacion[0] == sum(n in ESTACIONES) estacion_muerta[n]; 
 	
 }