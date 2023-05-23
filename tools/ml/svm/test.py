import subprocess
import xml.etree.ElementTree as ET
import json
from sklearn.svm import SVC
import pandas as pd
import pickle
import numpy as np
from sklearn.pipeline import make_pipeline
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import confusion_matrix
import sys
from xml.dom import minidom


def get_graph2vec_feature(graph2vec_inp, xml_loc):

    print("Parsing xml")


    max_start_time = 101

    tree = ET.parse(xml_loc)

    root = tree.getroot()


    queue = []
    revdic = {}



    dictionary = []

    i = 0

    while i < max_start_time:
        dictionary.append(str(i))
        i += 1
    queue.append(root)

    while queue:
        node = queue[0]
        queue = queue[1:]
        if node.text not in dictionary:
            dictionary.append(node.text)
        for child in node:
            queue.append(child)

    i = 0
    while i < len(dictionary):
        revdic[dictionary[i]] = i
        i += 1

    queue.append(root)
    ind_queue = [0]
    i = 0
    features_dic = {}
    edgelis = []
    while queue:
        node = queue[0]
        ind = ind_queue[0]
        queue = queue[1:]
        ind_queue = ind_queue[1:]
        features_dic[ind] = revdic[node.text]
        for child in node:
            i += 1
            edgelis.append([ind, i])
            queue.append(child)
            ind_queue.append(i)
    res = {}
    res["edges"] = edgelis
    res["features"] = features_dic

    json_string = json.dumps(res)
    oup = open(graph2vec_inp + "0.json", "w")
    oup.write(json_string)
    oup.close()


    print("Done")


test_xml = sys.argv[1] #Location of the test xml. xml_data_test/New_Schedule500.xml
graph2vec_input = sys.argv[2] #Where to store the input for the graph2vec algorithm. "dataset_test/"
graph2vec_output = sys.argv[3] #Where to store the output for the graph2vec algorithm. "features/nci2.csv"
svm_model_loc = sys.argv[4] #Where to save the SVM model. "SVM.model"
graph2vec_loc = sys.argv[5] #location of the praph2vec library. "graph2vec1/src/graph2vec.py"
save_path_file = sys.argv[6] #Where to store the prediction of whether properties hold. "prediction.xml"

#labels = pickle.load(open("labels", "rb"))
get_graph2vec_feature(graph2vec_input, test_xml)

command = "python " + graph2vec_loc + " --input-path " + graph2vec_input + " --output-path " + graph2vec_output
ret = subprocess.run(command, capture_output=True, shell=True)
print(ret)

df = pd.read_csv(graph2vec_output)

X = df.to_numpy()
X = X[:, 1:]

root = minidom.Document()

xml = root.createElement('root')
root.appendChild(xml)

i = 1
flag = 1
while i < y.shape[1]:

    clf = pickle.load(open(svm_model_loc + str(i), "rb"))

    y_hat = clf.predict(X)


    
    if y_hat == 0:
        stri =  "The property P" + str(i) + " does not hold"
        flag = 0
    else:
        stri = "The property P" + str(i) + " hold"



    productChild = root.createElement('Prediction')
    productChild.setAttribute('result', stri)

    xml.appendChild(productChild)

    i += 1

if flag == 0:
        stri =  "Not all property hold"
else:
    stri = "All property hold"

productChild = root.createElement('Prediction')
productChild.setAttribute('result', stri)

xml.appendChild(productChild)
xml_str = root.toprettyxml(indent="\t")



with open(save_path_file, "w") as f:
    f.write(xml_str)