## Prerequisite
- Python 3.9
- sklearn 
  - pip3 install sklearn
- pandas
  - pip3 install pandas
- networkx
  - pip3 install networkx
- tqdm
  - pip3 install tqdm  
- gensim
  - pip3 install gensim
## Build svm model
```python train.py ```

However here are the list of parameters which is hard coded for now.
  - n_files = 500 #number of xml files in dataset
  
 - verdict_loc = "/home/chi/Programs/VERDICT/extern/verdict-bundle-app-1.0.0-SNAPSHOT-capsule.jar" # location of verdict jar
  
 - kind2_loc = "/home/chi/Programs/VERDICT/extern/nix/kind2" #location of kind2 binary
  
-  xml_prefix = "xml_data/New_schedule" #location and the name of the xml files. Now it is xml_data/New_schedule0.xml to xml_data/New_schedule499.xml
  
-  crv_prefix = "tmp/crv_output" #location to save the crv_output
  
-  graph2vec_input = "dataset/" #location to save the input to the graph2vec library
  
-  graph2vec_output = "features/nci1.csv" #location to save the output of the graph2vec library
  
-  svm_model_loc = "SVM.model" #location to save the SVM model
  
-  graph2vec_loc = "graph2vec1/src/graph2vec.py" #location where graph2vec library is installed
  
-  test_split = 0.9 #the train/test split

## Run the svm model
- Input: an input XML file generated by OYSTER
- Output: a XML file containing valid or invalid property classification

```python test.py /path/to/the/xml_file```


## Generate a XML based on the SVM model
- Input: an input XML file generated by OYSTER
- Output: a XML file that should pass the SMT

- n_files = sys.argv[1] # Number of xml files in the training and validation dataset. 500
- train_prefix = sys.argv[2] #Location and name of the xml files. if the input is "xml_data/New_schedule" and n_files=500 the expected xml file name is from xml_data/New_schedule0.xml to xml_data/New_schedule499.xml
- graph2vec_input = sys.argv[3] #Where to store the input for the graph2vec algorithm. "dataset/"
- graph2vec_output = sys.argv[4] #Where to store the output for the graph2vec algorithm. "features/nci1.csv"
- graph2vec_loc = sys.argv[5] # location of the praph2vec library. "graph2vec1/src/graph2vec.py"
- suggestion_path = sys.argv[6]# where to save the suggestion xml. "suggestion.xml"


## Building Dockerfile
- Navigate into folder where OYSTER repo is located on your local filesystem
- ```shell
  cd OYSTER/tools/ml/svm
  docker build -t oyster-ml ./
  ```

  

