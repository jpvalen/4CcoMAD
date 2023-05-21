#### CORRELATION CONECTED CLUSTER---4CcoMAD---###

#### INFORMACIÓN GENERAL ####  
# Autores: Juan Pablo Valencia Arango y Nicolás Moreno Reyes
# Fecha: 1 de abril de 2022
# Última actualización: 18 de abril de 2022
# Versión: 1.0.1
# Descripción: Este script construye la metodología 4CcoMAD que une dos paper: 
#              Computing Clusters of Correlation Connected Objects
#              Christian Bohm, Karin Kailing, Peer Kroger, Arthur Zimek
#
#               On coMADs and Principal Component Analysis. 
#               Daniyal Kazempour(B), M. A. X. H unem order, and Thomas Seidl


##############################################################
## NOTA: ESTE SCRIPT CONTIENE LAS FUNCIONES FINALES PARA 4C ##
##############################################################

#### SECTION 1: INSTALL AND LOAD PACKAGES ####
library(dplyr);library(tidyr);library(ggplot2);library(gridExtra)
library(energy); library(caret); library(class);library(readxl)
library(neighbr);library(knitr);library(factoextra);library(fpc)
library(dbscan);library(gpairs);library(rlist);library(pipeR)
library(scatterplot3d); library(MASS);library(plotly);library(parallel)

#### FUNCIÓN GLOBAL ####
#Definición de parámetros globales
deltat<-0.01;lambda<-3;ka<-50;deltaNatural<-2;e<-3;mu<-3;u<-mu 
NumColsD <- ncol(D) #Sirve para filtrar más adelante las variables

func.jpva.EjecutaTodo <- function(D,NunColsD,deltat,lambda,ka,deltaNatural,e,mu,u,ejecucion){
  t0_INICIOTODO <- Sys.time()
  
  #### FUNCIONES AUXILIARES ####
  ### I. Función auxiliar para calcular la distancia euclideana.
  euclidean <- function(a, b) sqrt(sum((a - b)^2))
  ### II. Distancia euclidiana entre dos puntos ###
  # Description: Esta función calcula la distancia euclidea
  #              entre dos puntos P y Q.
  #                         
  # Input:   P: Punto inicial.
  #        Q: Punto final.
  #        M_p: Matriz de varianzas asociado a P.
  # Output: lista que contiene la siguiente información:
  #         1- distancia euclideana de P a Q.
  #            Nombre en lista: distanciaPQ
  func.jpva.DistP <- function(P,Q,MPGorro){
    PmenosQ <- as.matrix((P-Q))
    distanciaPQ <- sqrt((PmenosQ)%*%MPGorro%*%(t(PmenosQ)))
    return(distanciaPQ)
  }
  
  ### III. Función coMAD ###
  # Description: Esta función replica el paper de coMAD
  #                         
  # Input:   df:
  #        
  # Output: coMAD:Matrix
  func.jpva.coMAD <- function(df){
    res<-data.frame()
    for(i in 1:ncol(df)){
      Ai<-(df[,i]-median(df[,i]))
      for(j in 1:ncol(df)){
        Aj<-(df[,j]-median(df[,j]))
        comAiAj <- median(Ai*Aj)
        res[i,j] <- comAiAj
      }
    }
    colnames(res) <- colnames(df)
    return(coMAD=as.matrix(res))
  }
  
  #### INICIO de la función de insumos generales para el método ####
  
  #### Función interna 1: e-neighboors ####
  # Description: Esta función calcula los eps-vecinos de un punto O dados
  #              un epsilon, un mu y un df de referencia. Adicionalmente, define
  #              si ese punto O es un core_object.
  #                         
  # Input:   df: data frame original.
  #        O: punto particular sobre el que se desea indagar si es core_object.
  #        e: radio de la bola generada por el centro O.
  #        mu: total de vecinos, N, que mínimamente se requieren para que O sea 
  #            considerado un core_object.
  # Output: lista que contiene la siguiente información:
  #         1-Punto O de interés. 
  #           Nombre en lista: O_Generico
  #         2-Epsilon-Vecinos del punto O de interés. 
  #           Nombre en lista: VecinosOGenerico
  #         3-Flag que identifica si el punto es core object. 
  #           Nombre en lista: FlagCore_OGenerico
  func.jpva.Reformulada1.EpsCoreObjectValVec<-function(df,O,epsilon,mu){
    
    #### Función interna 1: e-neighboors ####
    # Description: Esta función calcula los eps-vecinos de un punto O dados
    #              un epsilon, un mu y un df de referencia. Adicionalmente, define
    #              si ese punto O es un core_object.
    #                         
    # Input:   df: data frame original.
    #        O: punto particular sobre el que se desea indagar si es core_object.
    #        e: radio de la bola generada por el centro O.
    #        mu: total de vecinos, N, que mínimamente se requieren para que O sea 
    #            considerado un core_object.
    # Output: lista que contiene la siguiente información:
    #         1-Punto O de interés. 
    #           Nombre en lista: O_Generico
    #         2-Epsilon-Vecinos del punto O de interés. 
    #           Nombre en lista: VecinosOGenerico
    #         3-Flag que identifica si el punto es core object. 
    #           Nombre en lista: FlagCore_OGenerico
    # O <- D[14,]
    O.Original <- O
    O <- as.matrix(O)
    #Creación automática del nombre de las variables que están en el df
    numVar <- seq(1:length(O))
    variables <- toString(paste('x[',numVar,']'))
    variables <- paste0('c(',variables,')')   
    variablesF <- (list(noquote(paste(variables,collapse = ",")))[[1]])
    #ACÁ HACE FALTA RESOLVER EL TEMA DE LAS VARIABLES, SIRVE PARA 3
    disEuc <- apply(df, 1, function(x){euclidean(c(x[1],x[2],x[3]),O)})
    dentroBola <- ifelse(disEuc <= e, 1,0)
    temp_df_dentroBola <- cbind(df, dentroBola)
    temp_df_dentroBola <- as.data.frame(temp_df_dentroBola)
    EpsVecinos_O <- dplyr::filter(temp_df_dentroBola,dentroBola == 1)
    CoreObject_O <- ifelse(sum(EpsVecinos_O$dentroBola)>=u,
                           'CoreObject','NoCoreObject')
    
    #Parte 2
    if(CoreObject_O == 'CoreObject' ){
      #### Function 2: Eigen values and eigen vectors ####
      # Description: Esta función calcula, a partir de un data frame particular la
      #              descomposición en valores y vectores propios tradicional y 
      #              transformada propuesta en el paper 4C, al igual que calcula la
      #              dimensión de correlación y si el conjunto es o no CorSet.
      #                       
      # Input:   df: data frame al que se le quiere calcular las matrices
      #        de valores y vectores propios.
      #        ka: constante de transformación que se usa para cambiar el peso de los 
      #            que tienen una baja varianza.Se recomienda que sea ka=50.
      #        lambda: dimensión en la que se desea analizar. Número natural y debe 
      #                ser menor que la dimensión del conjunto de datos original.
      # Output: lista que contiene la siguiente información:
      #         1-Matriz de valores propios asociados a la matriz de varianzas que
      #           se calcula sobde el df de interés.
      #           Nombre en lista: MatrizValoresPropios
      #         2-Matriz de vectores propios asoaciado a la matriz de varianzas que
      #           se calcula sobre el df de interés.
      #           Nombre en lista: MatrizVectoresPropios
      #         3-Valores propios asociados a la matriz de varianzas que se calcula
      #           sobre el df de interés.
      #           Nombre en lista: ValoresPropios
      #         4-Matriz de valores propios gorro, obtenidos al aplicar la 
      #           transformación definida a partir de ka. 
      #           Nombre en lista. MatrizValoresPropiosGorro
      #         5-MatrizGorro que se obtiene al crear el producto entre la matriz de 
      #           valores propios gorro y la matriz de vectores propios originales.
      #           Nombre en lista. MatrizPGorro
      #         6-Dimensión de la correlación obtenida a partir de los valores propios
      #           asociados a la matriz de varianzas que se calcula sobre el df de 
      #           interés. 
      #           Nombre en lista:CorDimS
      #         7-CorSet que es una marca que define si el conjunto de interés cumple 
      #           con la definición corset del paper 4C. 
      #           Nombre en lista:CorSet
      d <- (ncol(EpsVecinos_O)-1)
      MatCov <- cov(dplyr::select(EpsVecinos_O,-'dentroBola'))
      tempValProVecPro <- eigen(MatCov)
      ValPro <- tempValProVecPro$values
      MatValPro <- diag(tempValProVecPro$values)
      MatVecPro <- tempValProVecPro$vectors
      Omega_EV_i <- ValPro / ValPro[1]
      MatValProGorro <- diag(ifelse(Omega_EV_i > deltat,1,ka))
      MatPGorro <- MatVecPro %*% MatValProGorro %*% t(MatVecPro)
      CorDimS <- sum(ifelse(ValPro > deltaNatural,1,0))
      CorSet <- ifelse(sum(abs(ifelse(Omega_EV_i <= deltat,1,0))) >= (d-lambda),
                       'CorSet','NoCorSet')
      
      
      #Parte nueva: Aporte Profe Nicolás y JPVA
      coMAD <- func.jpva.coMAD(df=dplyr::select(EpsVecinos_O,-'dentroBola'))
      tempValProVecProcoMAD <- eigen(coMAD)
      ValProcoMAD <- tempValProVecProcoMAD$values
      MatValProcoMAD <- diag(tempValProVecProcoMAD$values)
      MatVecProcoMAD <- tempValProVecProcoMAD$vectors
      Omega_EV_i_coMAD <- ValProcoMAD / ValProcoMAD[1]
      MatValProGorrocoMAD <- diag(ifelse(Omega_EV_i_coMAD > deltat,1,ka))
      MatPGorrocoMAD <- MatVecProcoMAD %*% MatValProGorrocoMAD %*% t(MatVecProcoMAD)
      CorDimS <- sum(ifelse(ValPro > deltaNatural,1,0))
      CorSet <- ifelse(sum(abs(ifelse(Omega_EV_i <= deltat,1,0))) >= (d-lambda),
                       'CorSet','NoCorSet')
    } else {
      CoreObject_O
    }
    return(list(OGenerico=O.Original,
                VecinosOGenerico=EpsVecinos_O,
                FlagCore_OGenerico=CoreObject_O,
                MatrizValoresPropios=MatValPro,
                MatrizVectoresPropios=MatVecPro,
                ValoresPropios=ValPro,
                MatrizValoresPropiosGorro=MatValProGorro,
                MatrizPGorro = MatPGorro,
                CorDimS=CorDimS,
                CorSet=CorSet,
                coMAD=coMAD,
                tempValProVecProcoMAD=tempValProVecProcoMAD,
                ValProcoMAD=ValProcoMAD,
                MatValProcoMAD=MatValProcoMAD,
                MatVecProcoMAD=MatVecProcoMAD,
                Omega_EV_i_coMAD=Omega_EV_i_coMAD,
                MatValProGorrocoMAD=MatValProGorrocoMAD,
                MatPGorrocoMAD=MatPGorrocoMAD))
  }
  
  ##EJECUCIÓN FUNCIÓN 1: Genera todas las listas con la primera parte de las definiciones necesarias
  df <- D
  Res<- apply(D,1,FUN=func.jpva.Reformulada1.EpsCoreObjectValVec,df=D,epsilon=e,mu=mu)
  #### FIN de la función de insumos generales para el método ####
  
  #### INICIO de la función de distancia máxima ####
  ##Descripción: Calcula la distancia máxima y los epsilon-cor vecinos de O.
  #Distancia de P a Q
  PGenerico <- NULL
  EpsilonCor_VecinosLista <- NULL
  for(i in 1:nrow(D)){ #Inicio del for i
    P<-t(Res[[i]]$OGenerico)
    PGenerico[[i]] <- P
    Q <- as.data.frame(Res[[i]]$VecinosOGenerico[,-ncol(Res[[i]]$VecinosOGenerico)])
    distPQ<-apply(Q,1,func.jpva.DistP,P=P,MPGorro = Res[[i]]$MatPGorrocoMAD)
    #Distancia de Q a P. Solo cambia MatrizPGorro por MatrizQGorro
    distQP <- data.frame()
    for(j in 1:nrow(Q)){#Inicio del for j
      MatrizQGorro <- rlist::list.filter(Res,
                                         OGenerico[[1]] == Q[j,1] & OGenerico[[2]] == Q[j,2] )
      MatrizQGorro <- MatrizQGorro[[1]]$MatPGorrocoMAD
      distQPt<-apply(Q[j,],1,func.jpva.DistP,P=P,MPGorro = MatrizQGorro)
      distQP[j,1] <- distQPt
    } #Fin del for j
    colnames(distQP) <-'dQP'
    distanciaMax <- data.frame(Q=Q,P=P,dPQ=distPQ,dQP=distQP$dQP)
    dMax <- apply(distanciaMax[,c('dPQ','dQP')],1,max)
    distanciaMax <- dplyr::mutate(distanciaMax,DistMax=dMax)
    distanciaMax <- dplyr::mutate(distanciaMax,
                                  BanderaCoreCor= ifelse(distanciaMax$DistMax <= e, 1,0))
    distanciaMax <- dplyr::filter(distanciaMax,BanderaCoreCor == 1)
    EpsilonCor_Vecinos <- dplyr::select(distanciaMax,1:NumColsD,NumColsD:(NumColsD+NumColsD))
    EpsilonCor_VecinosLista[[i]] <- list(PuntoO=P,EpsilonCor_Vecinos = EpsilonCor_Vecinos)
  }#Fin del for i
  #### Fin de la función de distancia máxima ####
  
  #### INICIA identificación de Core_Cor_Den(O) basado en insumos previos.
  # Para determinar si los puntos O son o no CoreCorDen
  MaxCol <- ncol(EpsilonCor_VecinosLista[[1]]$EpsilonCor_Vecinos) # No importa el número de la lista
  # porque todas tienen la misma dim
  MinCol <- NumColsD +1
  df.OCoreCorDen <- data.frame()
  #Encuentra el punto O que se está buscando
  
  for(i in 1:nrow(D)){#Inicio del for
    cat('Iteración i:');print(i)
    tempO<-Res[[i]]$OGenerico
    tempO_DistMax <- EpsilonCor_VecinosLista[[i]]$PuntoO
    if(tempO ==tempO_DistMax ){ #Inicio del if
      CorsetO <- Res[[i]]$CorSet
      CorEpsVec <- ifelse(nrow(EpsilonCor_VecinosLista[[i]]$EpsilonCor_Vecinos)>=mu,1,0)
    }
    #else{stop()}#Fin del if
    df.resTemp <- as.data.frame(matrix(tempO,ncol = NumColsD))
    colnames(df.resTemp) <- colnames(D)
    df.resTemp2 <- cbind(df.resTemp,CorsetO,CorEpsVec)
    df.OCoreCorDen <- rbind(df.OCoreCorDen,df.resTemp2)
  }#Fin del for
  df.OCoreCorDen$MarcaCoreCorDen <- ifelse((df.OCoreCorDen$CorsetO =='CorSet' & df.OCoreCorDen$CorEpsVec == 1),
                                           'CoreCorDen','NoCoreCorDen')
  
  # La base de datos df.OCoreCorDen tiene todos los puntos O en D marcados si son
  # o no Core_CorDen
  # Los que NO son CoreCorDen se ponen en ClusterID=99
  
  df.OCoreCorDen$ClusterID <- ifelse(df.OCoreCorDen$MarcaCoreCorDen == 'NoCoreCorDen',99,0)
  df.OCoreCorDen_EtapaFinal <- dplyr::select(df.OCoreCorDen,1:NumColsD,ClusterID)
  df.OCoreCorDen_EtapaFinalNoise <- dplyr::filter(df.OCoreCorDen_EtapaFinal,ClusterID == 99)
  df.OCoreCorDen_EtapaFinalNONoise <- dplyr::filter(df.OCoreCorDen_EtapaFinal, ClusterID!= 99)
  # Meter a todos los vecinos de O en Omega
  # Acá debe iniciar el for
  RFinalFFF <- NULL
  for(kk in 1:nrow(df.OCoreCorDen_EtapaFinalNONoise)){
    cat('Iteración kk:');print(kk);Sys.time()
    #genera NewClusterID
    tempClusterID<-filter(df.OCoreCorDen_EtapaFinal,ClusterID < 99) #ok
    ClusterIDActualizado <- max(tempClusterID$ClusterID) +1 #ok
    
    O <- df.OCoreCorDen_EtapaFinalNONoise[kk,];O <- dplyr::select(O,-ClusterID)#Acá cambiar el 1 por i
    cat('Imprime O');print(O);Sys.time()
    VecinosCoreCorDen_O <- rlist::list.filter(EpsilonCor_VecinosLista,
                                              #EpsilonCor_VecinosLista[[i]]$PuntoO[1] == O[[1]] &  EpsilonCor_VecinosLista[[i]]$PuntoO[2]==O[[2]] &  EpsilonCor_VecinosLista[[i]]$PuntoO[3] == O[[3]])
                                              PuntoO[1] == O[[1]] &  PuntoO[2]==O[[2]] &  PuntoO[3] == O[[3]]
                                              #&  PuntoO[4] == O[[4]] &  PuntoO[5] == O[[5]] 
    )
    
    #func.jpva.DirReachRenovada <-function(Q)
    df.Omega <- VecinosCoreCorDen_O[[1]]$EpsilonCor_Vecinos[,1:NumColsD] #OK
    colnames(df.Omega) <- colnames(D)
    
    kkk <- 0
    RFinalFF <- NULL
    RFinal <- data.frame()
    
    while(nrow(df.Omega)>0) {
      Q <- df.Omega[1,] #OK
      #RFinal <- NULL
      for(jj in 1:nrow(D)){
        print(jj);print(Sys.time())
        #1. CoreCor_CorDen(Q): 1 significa que Q es CoreCorDen
        df.OCoreCorDen_EtapaFinalNONoise <- as.data.frame(df.OCoreCorDen_EtapaFinalNONoise)
        Q <- as.data.frame(Q)
        QCoreCorDen <- ifelse(nrow(dplyr::inner_join(Q,df.OCoreCorDen_EtapaFinalNONoise,
                                                     by=c('x0','x1','x2')))==0,0,1)
        cat('Imprime QCoreCorDen');print(QCoreCorDen);print(Sys.time())
        # 2. X está en vecinos de NepsMGorroQ
        X <- D[jj,] # Acá se debe incluir un for
        X <- as.data.frame(t(X))
        df.Omega <- as.data.frame(df.Omega)
        XPerteneceCorEpsVec <- ifelse(nrow(dplyr::inner_join(X,df.Omega,by=c('x0','x1','x2')))==0,0,1)
        
        # 3. CorDim(NEpsVeci(P))
        ResTemp <- list.filter(Res,
                               OGenerico[[1]] == X[1,1] & OGenerico[[2]] == X[1,2] & OGenerico[[3]] == X[1,3] #&
                               # OGenerico[[4]] == X[1,4] & OGenerico[[5]] == X[1,5] 
        )
        
        CorDimEpsVecX <- ifelse(ResTemp[[1]]$CorDimS <= lambda,1,0)
        
        # Conclusión
        DirCorReach_P_Desde_Q <- ifelse(sum(QCoreCorDen,
                                            XPerteneceCorEpsVec,
                                            CorDimEpsVecX)==3,'DirCorReach',
                                        'NoDirCorReach')
        
        if(DirCorReach_P_Desde_Q == 'DirCorReach'){
          RFinal <- rbind(RFinal,X)
          RFinal <- as.data.frame(RFinal)
        }#Fin del if
      }#Fin del for jj
      RFinal2 <- dplyr::left_join(RFinal,df.OCoreCorDen_EtapaFinal,
                                  by=c('x0','x1','x2')) # Acá le pone la marca del cluster
      #                                                        a cada uno de los R
      RFinal2 <- unique(RFinal2)
      
      #Asigna a cluster los X en R
      for(i in 1:nrow(RFinal2)){
        try({
          nrow(RFinal2) == 0 
          
          RFinal2$ClusterID[i] <- ifelse(RFinal2$ClusterID[i] == 0 | RFinal2$ClusterID[i] == 99 , 
                                         RFinal2$ClusterID[i] <- ClusterIDActualizado,
                                         RFinal2$ClusterID[i])
          #IF paralelo
          RFinal2 <- as.data.frame(RFinal2)
          XAgregar <- filter(RFinal2[i,],ClusterID == 0)
          df.Omega <- rbind(df.Omega,XAgregar)
          
          
        }, silent=TRUE)
        
      }
      RFinalF <- RFinal2
      RFinalFF <- rbind(RFinalFF,RFinalF)
      cat('Imprime RFinalFF');Sys.time()
      df.Omega<-df.Omega[-1,]
      if(nrow(df.Omega)==0){ break } 
      kkk <- kkk +1 
      
    }#Fin del while
    RFinalFF <- unique(RFinalFF)
    RFinalFF <- as.data.frame(RFinalFF)
    dftempf <- dplyr::left_join(df.OCoreCorDen_EtapaFinal,
                                RFinalFF,
                                by=c('x0','x1','x2'))
    #print(dftempf)
    dftempf2 <- dplyr::mutate(dftempf,
                              ClusterID=case_when((dftempf$ClusterID.x ==99 & is.na(dftempf$ClusterID.y)) ~ 99,
                                                  (dftempf$ClusterID.y ==99 & is.na(dftempf$ClusterID.x)) ~ 99,
                                                  (dftempf$ClusterID.x >=0 & dftempf$ClusterID.x <99 & is.na(dftempf$ClusterID.y)) ~ dftempf$ClusterID.x,
                                                  (dftempf$ClusterID.x ==0 | dftempf$ClusterID.x ==99 & dftempf$ClusterID.y ==0 | dftempf$ClusterID.y ==99 ) ~ ClusterIDActualizado,
                                                  (dftempf$ClusterID.x ==99 & dftempf$ClusterID.y  >0 )~dftempf$ClusterID.y,
                                                  (dftempf$ClusterID.y ==99 & dftempf$ClusterID.x  >0 )~dftempf$ClusterID.x,
                                                  (dftempf$ClusterID.y == dftempf$ClusterID.x  & dftempf$ClusterID.y> 0 & dftempf$ClusterID.x > 0 & dftempf$ClusterID.y !=99 &dftempf$ClusterID.x !=99)~dftempf$ClusterID.x
                              ))
    df.OCoreCorDen_EtapaFinalFULLActualizado<- dplyr::select(dftempf2,1:NumColsD,ClusterID)
    df.OCoreCorDen_EtapaFinal <- df.OCoreCorDen_EtapaFinalFULLActualizado
    #print(df.OCoreCorDen_EtapaFinal)
    #RFinalFFF <- rbind(RFinalFFF,df.OCoreCorDen_EtapaFinal)
  }#Fin del for kk
  #Resultados
  TablaClas<-table(df.OCoreCorDen_EtapaFinal$ClusterID)
  
  Resultados_Ejecucion <- df.OCoreCorDen_EtapaFinal
  TablaResultados_Ejecucion <- table(Resultados_Ejecucion$ClusterID)
  # Gráficos resultados
  pairs(df.OCoreCorDen_EtapaFinal[,1:NumColsD],col=factor(df.OCoreCorDen_EtapaFinal$ClusterID),
        pch=19,
        main=paste0("Resultados Ejecucion",ejecucion))
  scatterplot3d(Resultados_Ejecucion,
                color=factor(Resultados_Ejecucion$ClusterID),
                pch=19,grid=TRUE, box=FALSE,angle=-60,
                main=paste0("Resultados Ejecucion ",ejecucion))
  
  t0_FINTODO_Ejecucion <- Sys.time() - t0_INICIOTODO  
  
  return(list(dfInicial=D,dfFinal=df.OCoreCorDen_EtapaFinal,
              TablaResultadosEjecucion=TablaResultados_Ejecucion,
              TiempoEjecucion=t0_FINTODO_Ejecucion))
}

