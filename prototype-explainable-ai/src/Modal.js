import React, { useState } from 'react';

async function getConfig(){
  let response = await fetch('./modal.json')
  let json = undefined

  if (response.ok){
    json = await response.json()
  }
  return json
}


function Modal() {

  const [state,setState] = useState("problem-type");
  const [modelTitle, setModelTitle] = useState("Choose a problem");
  const [problemsName, setFirstNameError] = useState(["Tiger, Left"]);
  const [emailAddress, setEmailAddress] = useState("");
  const [emailAddressError, setEmailAddressError] = useState("");
  const [submitted, setSubmitted] = useState(false);

  (async () => {
    let response = await fetch('./modal.json')
    let json = await response.json()
    console.log(json)
  })();

  return (  
    <div class="modal fade" id="exampleModal" tabindex="-1" aria-labelledby="exampleModalLabel" aria-hidden="true">
      <div class="modal-dialog">
        <div class="modal-content">
          <div class="modal-header">
            <h5 class="modal-title" id="exampleModalLabel">{modelTitle}</h5>
            <button type="button" class="btn-close" data-bs-dismiss="modal" aria-label="Close"></button>
          </div>
          <div class="modal-body">
            
      </div>
          <div class="modal-footer">
            <button type="button" class="btn btn-secondary" data-bs-dismiss="modal">Close</button>
            <button type="button" class="btn btn-primary">Save changes</button>
          </div>
        </div>
      </div>
    </div>
  )
}


export default Modal;

//react cycle: choose problem -> choose variable -> choose operator -> choose state -> continue? -> choose variable -> ... 