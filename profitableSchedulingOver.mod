# due file uno per under e uno per over
# Il problema è un problema di programmazione lineare intera, dovremo decidere come assegnare le macchine ai jobs
# in questa versione oversubscribed non è detto che ogni job sia assegnato ad una macchina, possono restare dei job non svolti






### DATI

param nJobs;
set jobs := 1..nJobs;

param macchine;
set m := 1..macchine;

param costi {jobs,m};                # ogni job ha dei costi per le varie macchine
param penalita {jobs};               # ogni job ha anche una penalità    (per caso oversubscribed)

param tempiLavorazione {jobs,m};     # tempi per ogni lavoro

param tempoDisponibile1 {m};
param tempoDisponibile2 {m};

param compatibilitaJM {jobs,m};       # compatibilità tra jobs e macchine, vale 1 se compatibili
param compatibilitaJJ {jobs,jobs};    # compatibilità tra jobs e jobs






### VARIABILI


# assegnamento jobs macchina
var x {jobs,m} binary;     # vale 1 se il job è assegnato alla macchina

var y {jobs} binary;       # vale 1 se il job non è svolto






### VINCOLI


# la macchina può fare più job, ma un job viene assegnato ad al massimo una macchina
# la macchina deve essere compatibile con il job


# ogni job deve essere assegnato al massimo ad una macchina
subject to jobMacchina {i in jobs} :                                                 
	sum {j in m} x[i,j] <= 1; 


 # se la macchina non è compatibile con il job, non posso assegnarlo a quella macchina
subject to jobMacchinaCompatibilita {i in jobs, j in m: compatibilitaJM[i,j] = 0 }: 
	 x[i,j] = 0;


# posso avere più job sulla stessa macchina, quindi non serve un vincolo che controlli che la sum dei valori di x in ogni colonna sia <= 1 , 
# però non posso avere job non compatibili tra loro nella stessa macchina

# per ogni job in ogni macchina vedo, se x[i,j] = 1   e x[k,j] = 1 allora sono entrambi assegnati alla stessa macchina e questo non vale se compjj[i,k] = 0
subject to jobJobCompatibilita {i in jobs, j in m, k in i+1..nJobs:   compatibilitaJJ[i,k] = 0  }:   
	  (x[i,j] + x[k,j]) <= 1 ;


# il vincolo nell modello over sarà con i tempi di lavorazione minori di quelli del parametro tempoDisponibile2
subject to tempiMassimi {j in m }:
	sum {i in jobs} x[i,j] *  tempiLavorazione[i,j]   <= tempoDisponibile2[j];


# con i vincoli fino a questo punto però non assegna nessun job a nessuna macchina perchè non sono obbligato ad assegnarli, devo minimizzare le penitenze dei job non assegnati


# metto una variabile per vedere quali job eseguo
subject to valoreY {i in jobs}:
	y[i] = 1- sum {j in m} x[i,j];   
	#  so già che la somma mi da 0 o 1 per il vincolo che impone che un lavoro non possa essere in più macchine
	# metto " 1 - sum " perchè mi è più comodo avere la variabile con 1 se il lavoro è ignorato e 0 se è svolto






### OBIETTIVO

# Si vuole trovare il modo di avere penalità minima, e assegnare i job rimanenti
# minimize z: sum {i in jobs} y[i]  *  penalita[i];

# oltre a questo però tra le soluzioni esistenti di penalità minima, si vuole quella a costo minimo
# posso dare un "peso" molto inferiore alla seconda parte e minimizzare la somma

minimize z :  sum {i in jobs} y[i]  *  penalita[i]    +   (0.0000000001) * sum {i in jobs, j in m} x[i,j] * costi[i,j];






###########################

data;


param nJobs := 9;
param macchine := 3;


param costi :  		1	2	 3 :=
	1				24	42	23
	2				30	45	23
	3				33	54	16
	4				37	45	18
	5				34	47	22
	6				31	42	25
	7				30	41	19
	8				28	47	15
	9				25	50	20;


param penalita :=
1	10
2	10
3	10
4	10
5	15
6	15
7	15
8	15
9	20;


param tempiLavorazione: 		1	2	3 :=
	1				100	95	107
	2				111	108	115
	3				98	96	103
	4				132	128	133
	5				120	118	119
	6				115	117	114
	7				142	145	140
	8				123	125	120
	9				90	95	88;


param tempoDisponibile1:=      # (undersubscribed)
1	380
2	360
3	350;               


param tempoDisponibile2:=      # (oversubscribed)
1	360
2	330
3	320;    


param compatibilitaJM :		1	2	3 :=
	1						1	0	1
	2						1	0	1
	3						1	1	1
	4						1	1	0
	5						1	1	0
	6						1	1	1
	7						1	1	1
	8						0	1	1
	9						0	1	1;


param compatibilitaJJ :	 1 2 3 4 5 6 7 8 9 :=
1	 1 0 1 1 1 1 1 1 1
2	 0 1 1 1 1 1 1 1 1
3	 1 1 1 0 1 1 1 1 1
4	 1 1 0 1 1 1 1 1 1
5	 1 1 1 1 1 0 1 1 1
6	 1 1 1 1 0 1 1 1 1
7	 1 1 1 1 1 1 1 0 0
8	 1 1 1 1 1 1 0 1 0
9	 1 1 1 1 1 1 0 0 1;


end;

