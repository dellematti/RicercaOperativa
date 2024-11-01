# due file uno per under e uno per over
# Il problema è un problema di programmazione lineare intera, dovremo decidere come assegnare le macchine ai jobs
# in questa versione undersubscribed ci aspettiamo nel file OUT di trovare che ogni job sia assegnato ad una macchina, non devono
# restare dei job non svolti






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






### VINCOLI


# la macchina può fare più job, ma un job viene assegnato ad una macchina solamente
# la macchina deve essere compatibile con il job
# nel caso undersubscribed ogni job DEVE essere assegnato ad una macchina


# ogni job deve essere assegnato al massimo ad una macchina
subject to jobMacchina {i in jobs} :                                                 
	sum {j in m} x[i,j] <= 1; 


# nel caso undersubscribed ogni job deve essere assegnato a esattamente una macchina (rende superfluo il vincolo precedente)
subject to jobMacchinaUndersubscribed {i in jobs} :                                  
	sum {j in m} x[i,j] = 1; 


 # se la macchina non è compatibile con il job, non posso assegnarlo a quella macchina
subject to jobMacchinaCompatibilita {i in jobs, j in m: compatibilitaJM[i,j] = 0 }: 
	 x[i,j] = 0;


# posso avere più job sulla stessa macchina, quindi non serve un vincolo che controlli che la sum dei valori di x in ogni colonna sia <= 1 , 
# però non posso avere job non compatibili tra loro nella stessa macchina


# per ogni job in ogni macchina vedo, se x[i,j] = 1   e x[k,j] = 1 allora sono entrambi assegnati alla stessa macchina e questo non vale se compjj[i,k] = 0
subject to jobJobCompatibilita {i in jobs, j in m, k in i+1..nJobs:   compatibilitaJJ[i,k] = 0  }:   
	  (x[i,j] + x[k,j]) <= 1 ;


# il vincolo nell modello under sarà con i tempi complessivi minori del parametro tempoDisponibile1
subject to tempiMassimi {j in m }:
	sum {i in jobs} x[i,j] *  tempiLavorazione[i,j]   <= tempoDisponibile1[j];






### OBIETTIVO

# Si vuole trovare il modo di eseguire tutti i jobs a minimo costo complessivo.
minimize z : sum{i in jobs, j in m} x[i,j] * costi[i,j];






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

