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
  const firstVariable = new Variable(1, modalConfig['variable']['buttonsName'])
  const [variableInUse, setVariableInUse] = useState([firstVariable])
  const [variableUsed, setVariableUsed] = useState(new Set())


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
      if (!variableUsed.has(id)) {
        variableUsed.add(id)
        const tmpVariables = variableInUse.sort((a, b) => b.id - a.id)
        const idNewVariable = tmpVariables[0].id + 1
        const stringNewVariable = "x" + idNewVariable
        const newVariable = new Variable(idNewVariable, stringNewVariable)
        setVariableInUse([...variableInUse, newVariable].sort((a,b) => a.id - b.id))
      }
    }

    if (nextState === "action-rule") {
      setButtonsName(modalConfig[nextState][_problemName]['buttonsName'])
    }
    else if (nextState === "state") {
      setButtonsName(modalConfig[nextState][problemName]['buttonsName'])
    }
    else if (nextState === "variable") {
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
                        <button type="button" key={buttonName.id} id={buttonName.id} className="btn btn-outline-primary btn-lg btn-block" onClick={event => goToNextState(event.target.id)}>{buttonName.name}</button>
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