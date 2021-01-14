// In the test instaces,
// The size of Driver-yes customer must not be equal to a capacity of vehicle.
using CP;
int nj= ...;
int ny= ...;
int nv=1;
int nd=1;
range Nodes = 1..nj*2+nv*2+ny*2; 
range Vehicles = 1..nv;
range Drivers = 1..nd;
int vCapa=...;
int Dist[Nodes][Nodes];
int jc=nj+ny;

tuple t_Job {
key int id;
	int x;
	int y; 
    int st;
    int de;
    int est;
    int lst; 
    string taskType;  //pkup, drop, start, end
    string jobType;  //cus, drv, veh
    string preference;  //yes, no, -
    int yesCus; 
};
{t_Job} Jobs = ...;
{t_Job} DrvPickJobs = { j | j in Jobs : j.jobType == "drv" && j.id<=jc };
{t_Job} NoJobs = { j | j in Jobs : j.taskType=="pkup" && j.jobType == "cus" && j.preference=="n" };
//{t_Job} DrvJobs = { j | j in Jobs : j.jobType == "drv"};

execute { 
for(var v=2;v<=nv;v++) {
    Jobs.add(jc*2+v*2-1,Jobs.get(jc*2+1).x, Jobs.get(jc*2+1).y, Jobs.get(jc*2+1).st,
		    Jobs.get(jc*2+1).de,Jobs.get(jc*2+1).est, Jobs.get(jc*2+1).lst, 
  		    Jobs.get(jc*2+1).taskType,Jobs.get(jc*2+1).jobType, Jobs.get(jc*2+1).preference,0); 
    Jobs.add(jc*2+v*2,Jobs.get(jc*2+2).x, Jobs.get(jc*2+2).y, Jobs.get(jc*2+2).st,
		    Jobs.get(jc*2+2).de,Jobs.get(jc*2+2).est, Jobs.get(jc*2+2).lst,
  		    Jobs.get(jc*2+2).taskType,Jobs.get(jc*2+2).jobType, Jobs.get(jc*2+2).preference,0); 
    }		       
//writeln(Jobs);    
};

tuple t_J2J_Travel {
	key int j1;
	key int j2;
	int tt;
};
{t_J2J_Travel} J2J_Travel;

execute { 
for(var i in Jobs)	for(var j in Jobs) {
if(i!=j) J2J_Travel.add(i.id,j.id, Opl.ftoi(Opl.round ( Opl.sqrt( (i.x-j.x)*(i.x-j.x)+(i.y-j.y)*(i.y-j.y))   )));
	}
};

execute { 
for(var i in Jobs)	for(var j in Jobs)
  Dist[i.id][j.id]= Opl.ftoi(Opl.round ( Opl.sqrt( (i.x-j.x)*(i.x-j.x)+(i.y-j.y)*(i.y-j.y))));
};

//dvar interval bVehicleUsed[Vehicles] optional;
dvar interval itvJob[j in Jobs] optional(j.jobType=="drv") size j.st  ; 
dvar interval itvJ2V[j in Jobs][Vehicles] optional;
dvar interval JobSpan[DrvPickJobs][Vehicles] optional;
dvar interval NoSpan[NoJobs][Vehicles] optional;
dvar interval DrvSpan[DrvPickJobs][Vehicles] optional;
dvar interval itvD2V[j in DrvPickJobs][Drivers][Vehicles] optional;

dvar sequence seqVeh[v in Vehicles] 
 		in 	  all(j in Jobs) itvJ2V[j][v]  
 		types all(j in Jobs) j.id; 
 			
dvar sequence seqDrv[d in Drivers] 
 		in 	  all(j in DrvPickJobs, v in Vehicles) itvD2V[j][d][v]; 	
 		 			
cumulFunction Loading[v in Vehicles] = 
 	sum(j in Jobs: j.de > 0 ) stepAtStart (itvJ2V[j][v], j.de   ) -
 	sum(j in Jobs: j.de < 0 ) stepAtStart (itvJ2V[j][v], -(j.de)) ;
 		
dexpr int totDistance =
    (sum(j in Jobs, v in Vehicles) Dist[j.id][typeOfNext(seqVeh[v], itvJ2V[j][v], j.id, j.id)]);	
    
dexpr int ManyVehicls = sum(v in Vehicles) max(j in DrvPickJobs) presenceOf(DrvSpan[j][v]);
dexpr int cmax  = max(j in Jobs: j.id>jc) endOf(itvJob[j]);

//dexpr int NoCusOverlapLen = sum(v in Vehicles,d in DrvPickJobs: v==1) overlapLength(DrvSpan[d][v],NoSpan[v]);
	  
execute {
  cp.param.TimeLimit = 100;
  cp.param.Workers = 3;
  cp.param.LogVerbosity=21;  
  cp.param.LogPeriod = 1000000;
  cp.param.TemporalRelaxation = "On";
  cp.param.NoOverlapInferenceLevel = "Extended"  
  var f = cp.factory;
  cp.setSearchPhases(f.searchPhase(itvJ2V)); //seqVeh itvJ2V itvJob
}

minimize cmax;
//( totDistance/1000);      
constraints {
forall(j in Jobs){
	alternative(itvJob[j], all(v in Vehicles) itvJ2V[j][v]);
	startOf(itvJob[j]) >= j.est;
	//startOf(itvJob[j]) <= j.lst;
}	
forall(j,jh in Jobs: j.id==jh.id-jc && jh.id<= jc*2) {
   endBeforeStart(itvJob[j],itvJob[jh], Dist[j.id][jh.id]); //valid constraint
   forall(v in Vehicles) 
       before(seqVeh[v],itvJ2V[j][v],itvJ2V[jh][v]);  
}

forall(v in Vehicles){  	
	noOverlap(seqVeh[v], J2J_Travel);
	Loading[v] <= vCapa;
}

//the same vehicle must be used to destination
forall(v in Vehicles, j,jh in Jobs: j.id==jh.id-jc && jh.id<= jc*2)
	presenceOf(itvJ2V[j][v])==presenceOf(itvJ2V[jh][v]);
    
forall(v in Vehicles,j in Jobs: jc*2+v==j.id ){ // Truck stars from depot 
	presenceOf(itvJ2V[j][v])==1;
	first(seqVeh[v],itvJ2V[j][v]); 
}		

forall(v in Vehicles,j in Jobs: jc*2+nv+v==j.id){  // Truck returns to depot at the end
	presenceOf(itvJ2V[j][v])==1;
	last (seqVeh[v],itvJ2V[j][v]);  
}

forall(d in DrvPickJobs,v in Vehicles)
	span(JobSpan[d][v], all(j in Jobs:j.jobType=="cus" && (d.yesCus==j.id || d.yesCus+jc ==j.id)) itvJ2V[j][v]);
	
forall(n in NoJobs, v in Vehicles)
	span(NoSpan[n][v], all(j in Jobs:j.jobType=="cus" && (n.id==j.id || n.id+jc ==j.id)) itvJ2V[j][v]);
	
forall(d in DrvPickJobs,v in Vehicles)
	span(DrvSpan[d][v], all(j in Jobs:j.jobType=="drv" && (d.id==j.id || d.id+jc==j.id )) itvJ2V[j][v]);

forall(d1 in DrvPickJobs,v in Vehicles)
	sum(d2 in DrvPickJobs) (overlapLength(JobSpan[d1][v],  DrvSpan[d2][v]) >= sizeOf(JobSpan[d1][v])) >=1;
	
forall(j in DrvPickJobs,v in Vehicles)
	alternative(DrvSpan[j][v], all(d in Drivers) itvD2V[j][d][v]);
forall(d in Drivers)  	
	noOverlap(seqDrv[d]);
	
	
//	ManyVehicls==1;

//Driver-yes	
//forall(v in Vehicles,j in Jobs:j.jobType=="cus" && j.preference=="y")
//	presenceOf(itvJ2V[j][v]) <= sum(d in Jobs: d.jobType=="drv") presenceOf(itvJ2V[d][v]);

forall(i,j in Jobs: i.id+jc==j.id && 
	i.jobType=="drv" && i.taskType=="pkup" && i.preference=="y" && 
	j.jobType=="drv" && j.taskType=="drop" && j.preference=="y" ) 
	sum(v in Vehicles,d in DrvPickJobs) 
	  (startOf(itvJ2V[i][v]) <= startOf(JobSpan[d][v])  && endOf(JobSpan[d][v]) <= endOf(itvJ2V[j][v])) >=1;
	
forall(j in Jobs:j.jobType=="cus" && j.taskType=="pkup" && j.preference=="y" )
	 sum(v in Vehicles,d in Jobs:  d.jobType=="drv" && d.taskType=="pkup" && d.preference=="y" )
	 (startOf(itvJ2V[d][v]) <= startOf(itvJ2V[j][v])) >=1;  

forall(j in Jobs:j.jobType=="cus" && j.taskType=="drop" && j.preference=="y" )
	 sum(v in Vehicles, d in Jobs:  d.jobType=="drv" && d.taskType=="drop" && d.preference=="y" )
	 (endOf(itvJ2V[j][v]) <= endOf(itvJ2V[d][v])) >=1;  

//Driver-No	
sum(v in Vehicles,d in DrvPickJobs, n in NoJobs) overlapLength(NoSpan[n][v],DrvSpan[d][v])==0;

/*
//Driver-No	
forall(v in Vehicles,jp,jd in Jobs, d in DrvPickJobs: jd.id==jp.id+jc && jp.id <= jc 
	  && jp.taskType=="pkup" && jp.jobType=="cus" && jp.preference=="n"
	  && jd.taskType=="drop" && jd.jobType=="cus" && jd.preference=="n") { 	  
	 (endOf(DrvSpan[d][v]) <= startOf(itvJ2V[jp][v])) +
	 (endOf(itvJ2V[jd][v]) <= startOf(DrvSpan[d][v])) ==1;  
	  //overlapLength(DrvSpan[d][v],itvJ2V[jp][v])==0;
	  //overlapLength(DrvSpan[d][v],itvJ2V[jd][v])==0;
	}
*/	 	
} 


execute {
// id,type,nd,sz,est,lst,sharing

//writeln("ManyVehicls ===", ManyVehicls);

writeln("v"+"\t" + "i" +"\t"+ "t" +"\t"+ "p" +"\t"  + "ty" +"\t" + "q" +"\t" + "est" + "  \t"+ "lst" + "  \t" + "s" + "  \t" + "e"  );

for (var v in Vehicles)  
  for (var j in Jobs) 
	if (  itvJ2V[j][v].present) 
      	writeln( v +"\t"+ j.id +"\t" + j.jobType +"\t" + j.preference +"\t"  + j.taskType +"\t" +  j.de +"\t"+ j.est+ "\t" + j.lst +"\t"+  itvJob[j].start +"\t"+  itvJob[j].end ) ;      	
}      