import React, { useState } from 'react';
import modalConfig from './modalConfig.js'

function Variable(id, str) {
    this.id = id
    this.name = str
}

function Modal() {

  //const configParsed = JSON.parse(modalConfig);
  const [state, setState] = useState("problem-type");
  const [problemName, setProblemName] = useState("")
  const [modelTitle, setModelTitle] = useState(modalConfig['problem-type'].title);
  const [buttonsName, setButtonsName] = useState(modalConfig['problem-type'].buttonsName);
  // const [variableInUse, setVariableInUse] = useState([...modalConfig['variable']['buttonsName']])
  const [variableInUse, setVariableInUse] = useState([JSON.stringify(new Variable(1, modalConfig['variable']['buttonsName']))])

  function goToNextState(id) {
    const nextState = modalConfig[state]['next']
    setState(nextState)

    let _problemName = ""
    if (state === "problem-type") {
      setProblemName(id)
      _problemName = id
    }

    setModelTitle(modalConfig[nextState]['title'])

    if (state === "variable") {
      const tmpSet = new Set(variableInUse).add(JSON.stringify(new Variable(parseInt(id),"x" + id)))
      let variablesArr = [...tmpSet].sort((a,b) => b.id - a.id)
      console.log(variablesArr)
      let greatesVariable = variablesArr[0]
      let newVariable = "x" + (greatesVariable.id + 1)
      console.log(newVariable)
      let variables = [...tmpSet, newVariable]
      setVariableInUse(variables)
    }

    if (nextState === "action-rule") {
      setButtonsName(modalConfig[nextState][_problemName]['buttonsName'])
    }
    else if (nextState === "state") {
      setButtonsName(modalConfig[nextState][problemName]['buttonsName'])
    }
    else if (nextState === "variable") {
      console.log(variableInUse)
      setButtonsName(variableInUse)
    }
    else {
      setButtonsName(modalConfig[nextState]['buttonsName'])
    }

  }

  return (
    <div className="modal fade" id="exampleModal" tabIndex="-1" aria-labelledby="exampleModalLabel" aria-hidden="true">
      <div className="modal-dialog">
        <div className="modal-content">
          <div className="modal-header text-center">
            <h5 className="modal-title text-center" id="exampleModalLabel">{modelTitle}</h5>
            <button type="button" className="btn-close" data-bs-dismiss="modal" aria-label="Close"></button>
          </div>
          <div className="modal-body">
            <div className="container">
              <div className="row justify-content-center">
                <div className="btn-group" role="group" aria-label="Basic outlined example">
                  {buttonsName.map((buttonName) => {
                    if (state === "logic_connector" && buttonName === "I'm done") {
                      return (
                        <button type="button" key={buttonName} id={buttonName} data-bs-dismiss="modal" className="btn btn-outline-primary btn-lg btn-block" onClick={event => goToNextState(event.target.id)}>{buttonName}</button>
                      )
                    }
                    else if (state === "variable") {
                      return (
                        <button type="button" key={buttonName.id} id={buttonName.id} data-bs-dismiss="modal" className="btn btn-outline-primary btn-lg btn-block" onClick={event => goToNextState(event.target.id)}>{buttonName.name}</button>
                      )
                    }
                    else {
                      return (
                        <button type="button" key={buttonName} id={buttonName} className="btn btn-outline-primary btn-lg btn-block" onClick={event => goToNextState(event.target.id)}>{buttonName}</button>
                      )
                    }
                  })}
                </div>
              </div>
            </div>
          </div>
          <div className="modal-footer">
            <button type="button" className="btn btn-primary" data-bs-dismiss="modal">View Rule</button>
          </div>
        </div>
      </div>
    </div>
  )
}


export default Modal;

//react cycle: choose problem -> choose variable -> choose operator -> choose state -> logic connector? -> choose variable -> ... 