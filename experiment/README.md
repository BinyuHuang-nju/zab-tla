# Result of model checking
> Our verification of Zab using model checking is in progress, and we have obtained part of data set.  
> We plan to show our result in this doc and the doc is currently not complete. 

## Experiment configuration
In all experiments, we set CONSTANTS to model value except *Server* and *Value*. We adjust the set of servers *Server* and the set of operations that client request *Value* in different experiments. We set *Server* and *Value* as symmetrical model value to improve efficiency of verification of TLC. And we use 10 threads to do these experiments. We use *model-checking mode* and *simulation mode* respectively.  

Our statistical results include: diameter of the system states that have been traversed, the number of states that have been traversed, the number of different states that have been discovered, and the time spent in the experiment.

## Verification results of model checking  
|  Mode  |     TLC model         |    Diameter   |     num of states  | time of checking(hh:mm:ss)   |
| ----- | ---------------------- | ------------- | ------------------ | ---------------------------- |
| BFS   | (3 servers,2 rounds,2 transactions)    |             |       |  |
| Simulation | (3 servers,2 rounds,2 transactions)   |    -   |  20:15:11   | 10899460942 |
| 3     |   |    侍林天     |    |  |
| 4     |                         |         |   |    |
| 5     |                |        |     |   |
| 6     |                         |      |     |  |
| 7     |         |         |    |      |